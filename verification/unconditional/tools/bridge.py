#!/usr/bin/env python3
"""Build the independent bridge without writing either source checkout."""

import argparse
import concurrent.futures
import functools
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from evidence import identity
from scan import code_only

ROOT = Path(__file__).resolve().parents[1]
STATE = ROOT / ".bridge"
LIB = STATE / "build/lib/lean"
OVERLAY = STATE / "compatibility"
LOCK = json.loads((ROOT / "bridge-lock.json").read_text())
PACKAGES = json.loads((ROOT / "dependency-lock.json").read_text())["packages"]
PATCHES = json.loads((ROOT / "compatibility/patches.json").read_text())
PATCH_MODULES = {patch["module"] for patch in PATCHES}
IMPORT = re.compile(r"^\s*(?:public\s+|private\s+)?import\s+([^\n]+)", re.M)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def save_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2) + "\n")
    os.replace(temporary, path)


def git(path, *args):
    return subprocess.check_output(
        ["git", "--no-optional-locks", "-C", str(path), *args], text=True).strip()


def configuration():
    path = STATE / "config.json"
    if not path.exists():
        raise RuntimeError("Run tools/bridge.py configure with the three read-only input paths first.")
    return json.loads(path.read_text())


def verify_inputs(config):
    identities = {"numina": identity(Path(config["numina"]))}
    if digest(ROOT / "dependency-lock.json") != LOCK["numina_manifest_sha256"]:
        raise RuntimeError("The committed dependency lock differs from the Numina pin.")
    path = Path(config["bytedance"])
    head = git(path, "rev-parse", "HEAD")
    if head != LOCK["bytedance_commit"] or git(path, "status", "--porcelain"):
        raise RuntimeError(
            f"bytedance must be a clean checkout at {LOCK['bytedance_commit']}: {path}")
    identities["bytedance"] = head
    identities["upstream_source"] = identity(path)
    if (Path(config["numina"]) / "lean-toolchain").read_text().strip() != LOCK["toolchain"]:
        raise RuntimeError("The Numina toolchain differs from the lock.")
    manifest = Path(config["numina"]) / "lake-manifest.json"
    if digest(manifest) != LOCK["numina_manifest_sha256"]:
        raise RuntimeError("The Numina dependency manifest differs from the lock.")
    for package in PACKAGES:
        path = Path(config["packages"]) / package["name"]
        if git(path, "rev-parse", "HEAD") != package["rev"] or git(path, "status", "--porcelain"):
            raise RuntimeError(f"Dependency {package['name']} is not clean at {package['rev']}.")
        if package["name"] == "mathlib" and not (path / ".lake/build/lib/lean").is_dir():
            raise RuntimeError(f"Compile or populate the pinned dependency cache first: {path}")
        identities[package["name"]] = package["rev"]
    conditional = Path(config["numina"]) / ".lake/build/lib/lean/Kakeya.olean"
    if not conditional.is_file():
        raise RuntimeError(f"Compile the conditional library first (lake build Kakeya): {conditional}")
    version = subprocess.check_output([config["lean"], "--version"], text=True).strip()
    compiler_commit = subprocess.check_output([config["lean"], "--githash"], text=True).strip()
    if compiler_commit != LOCK["lean_githash"]:
        raise RuntimeError(f"Wrong Lean compiler: {version}")
    identities["compiler"] = version
    identities["compiler_sha256"] = digest(Path(config["lean"]))
    return identities


def overlays(config):
    for patch in PATCHES:
        relative = Path(patch["module"].replace(".", "/") + ".lean")
        original = Path(config["bytedance"]) / relative
        if digest(original) != patch["source_sha256"]:
            raise RuntimeError(f"Compatibility source drift: {original}")
        text = original.read_text()
        if text.count(patch["anchor"]) != 1:
            raise RuntimeError(f"Ambiguous compatibility insertion: {original}")
        text = text.replace(patch["anchor"], patch["anchor"] + patch["insert"], 1)
        if hashlib.sha256(text.encode()).hexdigest() != patch["output_sha256"]:
            raise RuntimeError(f"Compatibility output differs from verified overlay: {original}")
        output = OVERLAY / relative
        output.parent.mkdir(parents=True, exist_ok=True)
        if not output.exists() or output.read_text() != text:
            output.write_text(text)


def environment(config):
    env = dict(os.environ)
    libraries = ([LIB, Path(config["numina"]) / ".lake/build/lib/lean"]
                 + [Path(config["packages"]) / item["name"] / ".lake/build/lib/lean"
                    for item in PACKAGES])
    env["LEAN_PATH"] = os.pathsep.join(map(str, libraries))
    env["ELAN_TOOLCHAIN"] = LOCK["toolchain"]
    env["PATH"] = str(Path(config["lean"]).parent) + os.pathsep + env.get("PATH", "")
    return env


def source(config, module):
    relative = Path(module.replace(".", "/") + ".lean")
    overlay = OVERLAY / relative
    if module in PATCH_MODULES and overlay.exists():
        return overlay, OVERLAY
    namespace = module.split(".")[0]
    base = {"Unconditional": Path(config["numina"]),
            "MyLeanRepo": Path(config["bytedance"])}.get(namespace)
    return (base / relative, base) if base else (None, None)


@functools.lru_cache(maxsize=8192)
def parsed_imports(path, stamp):
    clean = code_only(path.read_text(encoding="utf-8"))
    return {name for line in IMPORT.findall(clean) for name in line.split()
            if re.fullmatch(r"[A-Za-z0-9_.]+", name)}


def imports(config, module):
    path, _ = source(config, module)
    stat = path.stat()
    return parsed_imports(path, (stat.st_size, stat.st_mtime_ns, stat.st_ctime_ns))


def closure(config, modules):
    graph = {}

    def visit(module):
        path, _ = source(config, module)
        if path is None or module in graph:
            return
        if not path.is_file():
            raise RuntimeError(f"Missing source module {module}: {path}")
        imported = imports(config, module)
        graph[module] = {name for name in imported if source(config, name)[0] is not None}
        for name in sorted(graph[module]):
            visit(name)

    for module in modules:
        if source(config, module)[0] is None:
            raise RuntimeError(f"Unknown root module: {module}")
        visit(module)
    return graph


def artifact(module):
    return LIB / (module.replace(".", "/") + ".olean")


def options_for(module):
    if module.startswith("MyLeanRepo."):
        return ["-DautoImplicit=false", "-Dlinter.all=false"]
    if module.startswith("Kakeya."):
        return ["-Dpp.unicode.fun=true", "-DrelaxedAutoImplicit=false", "-DmaxSynthPendingDepth=3"]
    return []


HASHES = {}


def artifact_hashes(path):
    """Include the private and IR fragments consumed by Lean 4.32."""
    result = {}
    for suffix in (".olean", ".olean.private", ".olean.server", ".ir"):
        file = path.with_suffix(suffix)
        if not file.exists():
            if suffix == ".olean":
                raise RuntimeError(f"Missing imported artifact: {file}")
            result[suffix] = None
            continue
        stat = file.stat()
        stamp = (stat.st_size, stat.st_mtime_ns, stat.st_ctime_ns)
        old = HASHES.get(file)
        if old is None or old[0] != stamp:
            HASHES[file] = (stamp, digest(file))
        result[suffix] = HASHES[file][1]
    return result


def dependency_artifact(config, module):
    relative = module.replace(".", "/") + ".olean"
    libraries = environment(config)["LEAN_PATH"].split(os.pathsep)
    libraries.append(str(Path(config["lean"]).parent.parent / "lib/lean"))
    for library in libraries:
        path = Path(library) / relative
        if path.is_file():
            return path
    raise RuntimeError(f"Missing compiled dependency: {module}")


def inputs(config, module):
    path, _ = source(config, module)
    return {"source_sha256": digest(path), "toolchain": LOCK["toolchain"],
            "compiler_sha256": digest(Path(config["lean"])), "options": options_for(module),
            "dependencies": {name: artifact_hashes(dependency_artifact(config, name))
                             for name in sorted(imports(config, module) | {"Init"})}}


def receipt(config, module, exit_code=0):
    record = {**inputs(config, module), "exit_code": exit_code}
    if exit_code == 0:
        record["artifacts"] = artifact_hashes(artifact(module))
    return record


def build(config, modules, jobs, rebuild=False):
    before = verify_inputs(config)
    save_json(STATE / "input-identities.json", before)
    overlays(config)
    graph = closure(config, modules)
    result_path = STATE / "build-results.json"
    records = json.loads(result_path.read_text()) if result_path.exists() else {}
    done, pending, failed, running = set(), set(graph), set(), {}
    env = environment(config)
    (STATE / "logs").mkdir(parents=True, exist_ok=True)

    def valid(module):
        if rebuild and module in modules:
            return False
        old = records.get(module, {})
        if old.get("exit_code") != 0 or not artifact(module).is_file():
            return False
        return old == {**old, **receipt(config, module)}

    def compile_one(module):
        before_inputs = inputs(config, module)
        path, base = source(config, module)
        output = artifact(module)
        output.parent.mkdir(parents=True, exist_ok=True)
        options = options_for(module)
        command = [config["lean"], "--tstack=8192", *options, "-R", str(base),
                   "-o", str(output), "-i", str(output.with_suffix(".ilean")), str(path)]
        log = STATE / "logs" / f"{module}.log"
        with log.open("w") as stream:
            result = subprocess.run(command, env=env, stdout=stream, stderr=subprocess.STDOUT)
        record = receipt(config, module, result.returncode)
        if before_inputs != inputs(config, module):
            record["exit_code"] = 1
            record["error"] = "Source or imported artifacts changed during compilation."
        record.update({"command": command, "log": str(log)})
        return record

    with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as pool:
        while pending or running:
            ready = sorted(name for name in pending if graph[name] <= done)
            for name in ready:
                if valid(name):
                    done.add(name)
                    pending.remove(name)
                elif len(running) < jobs:
                    running[pool.submit(compile_one, name)] = name
                    pending.remove(name)
            if not running:
                if ready:
                    continue
                break
            completed, _ = concurrent.futures.wait(running, return_when=concurrent.futures.FIRST_COMPLETED)
            for future in completed:
                name = running.pop(future)
                records[name] = future.result()
                if records[name]["exit_code"] == 0:
                    done.add(name)
                    print(f"PASS {name}", flush=True)
                else:
                    failed.add(name)
                    print(f"FAIL {name}: {records[name]['log']}", flush=True)
                save_json(result_path, records)
    if before != verify_inputs(config):
        raise RuntimeError("Verification inputs changed during the bridge build.")
    print(json.dumps({"compiled_or_cached": len(done), "failed": sorted(failed),
                      "blocked": sorted(pending)}), flush=True)
    return 1 if failed or pending else 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="action", required=True)
    configure = sub.add_parser("configure")
    configure.add_argument("--numina", type=Path, default=ROOT.parents[1])
    configure.add_argument("--bytedance", type=Path, default=ROOT.parents[1] / "upstream/3d-sticky-kakeya")
    for name in ("packages", "lean"):
        configure.add_argument("--" + name, type=Path, required=True)
    compile_parser = sub.add_parser("build")
    compile_parser.add_argument("modules", nargs="*", default=LOCK["default_modules"])
    compile_parser.add_argument("-j", "--jobs", type=int, default=2)
    compile_parser.add_argument("--rebuild", action="store_true", help="Recompile the named roots even when cached.")
    sub.add_parser("environment")
    sub.add_parser("verify-inputs")
    run_lean = sub.add_parser("lean")
    run_lean.add_argument("arguments", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    if args.action == "configure":
        config = {name: str(getattr(args, name).resolve())
                  for name in ("numina", "bytedance", "packages", "lean")}
        upstream = Path(config["bytedance"])
        if STATE.is_relative_to(upstream) or Path(config["packages"]).is_relative_to(upstream):
            raise RuntimeError("Bridge outputs and dependency caches must stay outside the second development.")
        identities = verify_inputs(config)
        save_json(STATE / "config.json", config)
        save_json(STATE / "input-identities.json", identities)
        overlays(config)
        print(json.dumps({"configured": str(ROOT), "inputs": identities}, indent=2))
        return 0
    config = configuration()
    if args.action == "build":
        if args.jobs < 1:
            parser.error("--jobs must be positive")
        return build(config, args.modules, args.jobs, args.rebuild)
    if args.action == "verify-inputs":
        print(json.dumps(verify_inputs(config), indent=2))
        return 0
    verify_inputs(config)
    env = environment(config)
    if args.action == "environment":
        for name in ("LEAN_PATH", "ELAN_TOOLCHAIN", "PATH"):
            print(f"export {name}={shlex.quote(env[name])}")
        return 0
    arguments = args.arguments[1:] if args.arguments[:1] == ["--"] else args.arguments
    command = [config["lean"], *arguments]
    os.execvpe(command[0], command, env)


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (RuntimeError, FileNotFoundError, subprocess.CalledProcessError) as error:
        print(f"bridge: {error}", file=sys.stderr)
        raise SystemExit(1)
