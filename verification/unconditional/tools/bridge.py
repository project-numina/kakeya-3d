#!/usr/bin/env python3
"""Build the independent bridge without writing either source checkout."""

import argparse
import concurrent.futures
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
STATE = ROOT / ".bridge"
LIB = STATE / "build/lib/lean"
OVERLAY = STATE / "compatibility"
LOCK = json.loads((ROOT / "bridge-lock.json").read_text())
PACKAGES = json.loads((ROOT / "dependency-lock.json").read_text())["packages"]
PATCHES = json.loads((ROOT / "compatibility/patches.json").read_text())
IMPORT = re.compile(r"^\s*(?:public\s+|private\s+)?import\s+([^\n]+)", re.M)
SUBMODULE = "upstream/3d-sticky-kakeya"


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


def submodule_revision(root, path):
    """The revision this repository records for `path`, or None when it is not a submodule."""
    try:
        entry = git(root, "ls-files", "-s", "--", path)
    except subprocess.CalledProcessError:
        return None
    if not entry or not entry.startswith("160000 "):
        return None
    return entry.split()[1]


def verify_inputs(config):
    identities = {}
    if digest(ROOT / "dependency-lock.json") != LOCK["numina_manifest_sha256"]:
        raise RuntimeError("The committed dependency lock differs from the Numina pin.")
    path = Path(config["bytedance"])
    head = git(path, "rev-parse", "HEAD")
    if head != LOCK["bytedance_commit"] or git(path, "status", "--porcelain"):
        raise RuntimeError(
            f"bytedance must be a clean checkout at {LOCK['bytedance_commit']}: {path}")
    identities["bytedance"] = head
    recorded = submodule_revision(Path(config["numina"]), SUBMODULE)
    if recorded is not None and recorded != LOCK["bytedance_commit"]:
        raise RuntimeError(
            f"The {SUBMODULE} submodule records {recorded}, not the reviewed pin "
            f"{LOCK['bytedance_commit']}. Update the lock and re-verify, or reset the submodule.")
    identities["bytedance_submodule"] = recorded
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
    if "4.32.0-rc1" not in version:
        raise RuntimeError(f"Wrong Lean compiler: {version}")
    identities["compiler"] = version
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
    if overlay.exists():
        return overlay, OVERLAY
    namespace = module.split(".")[0]
    base = {"Unconditional": Path(config["numina"]),
            "MyLeanRepo": Path(config["bytedance"])}.get(namespace)
    return (base / relative, base) if base else (None, None)


def closure(config, modules):
    graph = {}

    def visit(module):
        path, _ = source(config, module)
        if path is None or module in graph:
            return
        if not path.is_file():
            raise RuntimeError(f"Missing source module {module}: {path}")
        imported = [name for line in IMPORT.findall(path.read_text())
                    for name in line.split("--")[0].split()
                    if re.fullmatch(r"[A-Za-z0-9_.]+", name)]
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


def receipt(config, module, graph, exit_code=0):
    path, _ = source(config, module)
    record = {"source_sha256": digest(path), "exit_code": exit_code,
              "toolchain": LOCK["toolchain"], "options": options_for(module)}
    if exit_code == 0:
        record["olean_sha256"] = digest(artifact(module))
        record["dependencies"] = {name: digest(artifact(name)) for name in graph[module]}
    return record


def adopt(config, library):
    graph = closure(config, LOCK["default_modules"])
    records = {}
    for module in graph:
        existing = library / (module.replace(".", "/") + ".olean")
        if not existing.is_file():
            raise RuntimeError(f"Verified cache is incomplete: {existing}")
    for module in graph:
        relative = Path(module.replace(".", "/"))
        for suffix in (".olean", ".olean.private", ".olean.server", ".ir", ".ilean"):
            existing = library / (str(relative) + suffix)
            if existing.is_file():
                output = LIB / (str(relative) + suffix)
                output.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(existing, output)
    for module in graph:
        records[module] = receipt(config, module, graph)
        records[module]["origin"] = "adopted verified integration cache"
    save_json(STATE / "build-results.json", records)
    print(f"Adopted {len(records)} modules into {LIB}", flush=True)


def seed_upstream(config, library, receipts):
    verify_inputs(config)
    overlays(config)
    approved = {}
    for path in receipts:
        for module, record in json.loads(path.read_text()).items():
            if module.startswith("MyLeanRepo.") and record.get("exit_code") == 0:
                approved[module] = record
    graph = closure(config, sorted(approved))
    if set(graph) != set(approved):
        raise RuntimeError("Upstream receipts do not cover their complete project import closure.")
    for module, record in approved.items():
        path, _ = source(config, module)
        incoming = library / (module.replace(".", "/") + ".olean")
        if (record.get("source_sha256") != digest(path)
                or record.get("olean_sha256") != digest(incoming)
                or record.get("toolchain") != LOCK["toolchain"]
                or record.get("options") != options_for(module)):
            raise RuntimeError(f"Unverified upstream cache receipt: {module}")
    for module in graph:
        relative = module.replace(".", "/")
        for suffix in (".olean", ".olean.private", ".olean.server", ".ir", ".ilean"):
            incoming = library / (relative + suffix)
            if incoming.is_file():
                output = LIB / (relative + suffix)
                output.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(incoming, output)
    result_path = STATE / "build-results.json"
    records = json.loads(result_path.read_text()) if result_path.exists() else {}
    for module in graph:
        records[module] = {**receipt(config, module, graph), "origin": "verified upstream receipt handoff"}
    save_json(result_path, records)
    summary = {"okay": True, "seeded_upstream_modules": len(graph),
               "receipt_sha256": [digest(path) for path in receipts]}
    save_json(STATE / "upstream-handoff.json", summary)
    print(json.dumps(summary, indent=2), flush=True)


def build(config, modules, jobs, rebuild=False):
    verify_inputs(config)
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
        return old == {**old, **receipt(config, module, graph)}

    def compile_one(module):
        path, base = source(config, module)
        output = artifact(module)
        output.parent.mkdir(parents=True, exist_ok=True)
        options = options_for(module)
        command = [config["lean"], "--tstack=8192", *options, "-R", str(base),
                   "-o", str(output), "-i", str(output.with_suffix(".ilean")), str(path)]
        log = STATE / "logs" / f"{module}.log"
        with log.open("w") as stream:
            result = subprocess.run(command, env=env, stdout=stream, stderr=subprocess.STDOUT)
        record = receipt(config, module, graph, result.returncode)
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
    print(json.dumps({"compiled_or_cached": len(done), "failed": sorted(failed),
                      "blocked": sorted(pending)}), flush=True)
    return 1 if failed or pending else 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="action", required=True)
    configure = sub.add_parser("configure")
    configure.add_argument("--numina", type=Path, default=ROOT.parent / "kakeya")
    configure.add_argument("--bytedance", type=Path, default=ROOT.parent / "bd-sticky")
    for name in ("packages", "lean"):
        configure.add_argument("--" + name, type=Path, required=True)
    configure.add_argument("--verified-cache", type=Path)
    compile_parser = sub.add_parser("build")
    compile_parser.add_argument("modules", nargs="*", default=LOCK["default_modules"])
    compile_parser.add_argument("-j", "--jobs", type=int, default=8)
    compile_parser.add_argument("--rebuild", action="store_true", help="Recompile the named roots even when cached.")
    sub.add_parser("environment")
    sub.add_parser("verify-inputs")
    seed = sub.add_parser("seed-upstream")
    seed.add_argument("--library", type=Path, required=True)
    seed.add_argument("--receipts", type=Path, action="append", required=True)
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
        if args.verified_cache:
            adopt(config, args.verified_cache.resolve())
        print(json.dumps({"configured": str(ROOT), "inputs": identities}, indent=2))
        return 0
    config = configuration()
    if args.action == "seed-upstream":
        seed_upstream(config, args.library.resolve(), [path.resolve() for path in args.receipts])
        return 0
    if args.action == "build":
        if args.jobs < 1:
            parser.error("--jobs must be positive")
        return build(config, args.modules, args.jobs, args.rebuild)
    if args.action == "verify-inputs":
        print(json.dumps(verify_inputs(config), indent=2))
        return 0
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
