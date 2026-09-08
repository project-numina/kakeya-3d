#!/usr/bin/env python3
"""Run the pinned comparator against an independently frozen Kakeya challenge."""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys


sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from evidence import identity, save_json

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent

# The two challenges this driver can run. The conditional one states the main
# theorem with its hypothesis; the unconditional one states the bare conjecture
# and is discharged through the linking layer, whose compiled artifacts live in
# their own library root.
TARGETS = {
    "conditional": {
        "challenge": "Challenge.lean.in",
        "solution": "Solution.lean",
        "config": "config.json",
        "libraries": [],
        "required": ["Kakeya/DimensionThree/KakeyaConjecture.olean"],
    },
    "unconditional": {
        "challenge": "ChallengeUnconditional.lean.in",
        "solution": "SolutionUnconditional.lean",
        "config": "config-unconditional.json",
        "libraries": ["verification/unconditional/.bridge/build/lib/lean"],
        "required": ["Unconditional/KakeyaConjecture.olean"],
    },
}


def digest(file: Path) -> str:
    with file.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def capture(args: list[str], cwd: Path = ROOT) -> str:
    return subprocess.check_output(args, cwd=cwd, text=True).strip()


def run(args: list[str], cwd: Path = ROOT) -> None:
    print("Running: " + " ".join(args), flush=True)
    subprocess.run(args, cwd=cwd, check=True)


def checked_path(relative: str) -> Path:
    file = ROOT / relative
    if not file.resolve().is_relative_to(ROOT):
        raise RuntimeError(f"Path escapes the standalone repository: {relative}")
    return file


def verify_boundary() -> dict:
    manifest_file = HERE / "trusted-boundary.json"
    manifest = json.loads(manifest_file.read_text())
    if not manifest["sources"]:
        raise RuntimeError("The trusted boundary source inventory is empty")
    if (ROOT / "lean-toolchain").read_text().strip() != manifest["lean_toolchain"]:
        raise RuntimeError("The trusted boundary toolchain changed")
    if digest(ROOT / "lake-manifest.json") != manifest["lake_manifest_sha256"]:
        raise RuntimeError("The trusted boundary dependency manifest changed")
    if capture(["lean", "--githash"]) != manifest["lean_githash"]:
        raise RuntimeError("Lean has a different source revision")
    toolchain = Path(capture(["lean", "--print-prefix"])).resolve()
    for item in manifest["sources"]:
        if item["root"] == "project":
            base = ROOT
        elif item["root"] == "toolchain":
            base = toolchain
        elif item["root"].startswith("package:"):
            base = checked_path(".lake/packages/" + item["root"].split(":", 1)[1]).resolve()
        else:
            raise RuntimeError(f"Unknown trusted source root: {item['root']}")
        file = base / item["path"]
        if not file.resolve().is_relative_to(base):
            raise RuntimeError(f"Trusted source path escapes its root: {item['key']}")
        if digest(file) != item["sha256"]:
            raise RuntimeError(f"Frozen boundary source changed: {item['key']}")
    for item in manifest["packages"]:
        checkout = checked_path(f".lake/packages/{item['name']}")
        if capture(["git", "rev-parse", "HEAD"], checkout) != item["rev"]:
            raise RuntimeError(f"Dependency revision changed: {item['name']}")
        if capture(["git", "status", "--porcelain", "--untracked-files=no"], checkout):
            raise RuntimeError(f"Dependency has modified tracked sources: {item['name']}")
    return {"manifest_sha256": digest(manifest_file), "files": len(manifest["sources"])}


def source_inventory() -> dict[str, str]:
    names = subprocess.check_output(
        ["git", "ls-files", "-z", "--cached", "--others", "--exclude-standard", "--", "*.lean"],
        cwd=ROOT,
    ).decode().split("\0")
    return {name: digest(checked_path(name)) for name in sorted(set(filter(None, names)))}


def prepare_tools(pins: dict) -> tuple[Path, Path, Path]:
    checkout = ROOT / ".verify-work/tools/comparator"
    pinned = pins["comparator"]
    if not checkout.exists():
        checkout.parent.mkdir(parents=True, exist_ok=True)
        run(["git", "clone", "--depth", "1", "--branch", pinned["tag"], pinned["url"], str(checkout)])
    if capture(["git", "rev-parse", "HEAD"], checkout) != pinned["commit"]:
        raise RuntimeError("Comparator checkout has the wrong revision")
    if capture(["git", "status", "--porcelain", "--untracked-files=no"], checkout):
        raise RuntimeError("Comparator checkout has modified tracked sources")
    if digest(checkout / "lake-manifest.json") != pinned["manifest_sha256"]:
        raise RuntimeError("Comparator dependency manifest changed")
    if (checkout / "lean-toolchain").read_text().strip() != pins["toolchain"]:
        raise RuntimeError("Comparator toolchain differs from the project")
    run(["lake", "build", "lean4export", "comparator"], checkout)
    for name, commit in pins["dependencies"].items():
        dependency = checkout / ".lake/packages" / name
        if capture(["git", "rev-parse", "HEAD"], dependency) != commit:
            raise RuntimeError(f"Comparator dependency revision changed: {name}")
        if capture(["git", "status", "--porcelain", "--untracked-files=no"], dependency):
            raise RuntimeError(f"Comparator dependency has modified sources: {name}")
    return (checkout / ".lake/build/bin/comparator",
            checkout / ".lake/packages/lean4export/.lake/build/bin/lean4export",
            checkout / "scripts/fake-landrun.sh")


def validate_cache_tree(entry: Path, visited: set[Path] | None = None) -> None:
    if visited is None:
        visited = set()
    resolved = entry.resolve(strict=True)
    if not resolved.is_relative_to(ROOT):
        raise RuntimeError(f"Cache entry points outside this repository: {entry}")
    if resolved in visited:
        return
    visited.add(resolved)
    if resolved.is_dir():
        for child in resolved.iterdir():
            validate_cache_tree(child, visited)
    elif not resolved.is_file():
        raise RuntimeError(f"Cache entry is not a regular file or directory: {entry}")


def prepare_wrapper(wrapper: Path, target: dict, *, require_main: bool = True) -> None:
    library = wrapper / ".lake/build/lib/lean"
    library.mkdir(parents=True)
    roots = [ROOT / ".lake/build/lib/lean"]
    roots.extend(checked_path(name) for name in target["libraries"])
    roots.extend(sorted((ROOT / ".lake/packages").glob("*/.lake/build/lib/lean")))
    visited: set[Path] = set()
    for source_root in roots:
        if not source_root.exists() and not require_main:
            continue
        if not source_root.resolve().is_relative_to(ROOT):
            raise RuntimeError(f"Build root points outside this repository: {source_root}")
        for source in sorted(source_root.iterdir()):
            validate_cache_tree(source, visited)
            link = library / source.name
            if link.exists() or link.is_symlink():
                raise RuntimeError(f"Module collision in comparator cache view: {link.name}")
            link.symlink_to(source.resolve(), target_is_directory=source.is_dir())
    required_modules = ["Mathlib.olean"]
    if require_main:
        required_modules.extend(target["required"])
    for required in required_modules:
        if not (library / required).is_file():
            raise RuntimeError(f"Required compiled module is missing: {required}")
    shutil.copy2(HERE / "lakefile.toml", wrapper / "lakefile.toml")
    shutil.copy2(HERE / target["solution"], wrapper / "Solution.lean")
    shutil.copy2(HERE / target["config"], wrapper / "config.json")
    shutil.copy2(ROOT / "lean-toolchain", wrapper / "lean-toolchain")
    template = (HERE / target["challenge"]).read_text()
    marker = "@@COMPARATOR_TARGET_PROOF@@"
    if template.count(marker) != 1:
        raise RuntimeError("Challenge must contain exactly one protocol marker")
    (wrapper / "Challenge.lean").write_text(template.replace(marker, "by sorry"))


def bridge_evidence() -> dict:
    driver = "verification/unconditional/tools/bridge.py"
    return {"inputs": json.loads(capture([sys.executable, driver, "verify-inputs"])),
            "build_results_sha256": digest(ROOT / "verification/unconditional/.bridge/build-results.json")}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prepare-only", action="store_true", help="Prepare tools and wrapper; do not claim a comparator result")
    parser.add_argument("--challenge-only", action="store_true", help="Compile only the independent challenge specification")
    parser.add_argument("--jobs", type=int, default=2)
    parser.add_argument("--receipt-output", type=Path, help="Also write the final receipt to this path")
    parser.add_argument("--target", choices=sorted(TARGETS), default="conditional",
                        help="Which frozen challenge to replay")
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    project_before = identity(ROOT)
    target = TARGETS[args.target]
    pins = json.loads((HERE / "tools.json").read_text())
    if (ROOT / "lean-toolchain").read_text().strip() != pins["toolchain"]:
        raise RuntimeError("Project toolchain differs from the reviewed comparator pin")
    boundary = verify_boundary()
    if args.challenge_only:
        stamp = dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
        wrapper = ROOT / ".verify-work/challenge" / stamp
        prepare_wrapper(wrapper, target, require_main=False)
        run(["lake", "build", "Challenge"], wrapper)
        print(f"Challenge compilation passed: {wrapper}; full comparator has not run.", flush=True)
        return 0
    run([sys.executable, "verification/scan.py"])
    run(["lake", "build", "Kakeya", "FinalCheck"])
    if args.target == "unconditional":
        bridge = ["verification/unconditional/tools/bridge.py"]
        run([sys.executable, *bridge, "verify-inputs"])
        run([sys.executable, *bridge, "build", "Unconditional", "-j", str(args.jobs)])
        run([sys.executable, *bridge, "lean", "verification/unconditional/AxiomCheck.lean"])
    comparator, exporter, landrun = prepare_tools(pins)
    stamp = dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    wrapper = ROOT / ".verify-work/comparator" / stamp
    prepare_wrapper(wrapper, target)
    if identity(ROOT) != project_before:
        raise RuntimeError("Project sources changed while preparing the comparator.")
    source_before = source_inventory()
    bridge_before = bridge_evidence() if args.target == "unconditional" else None
    before_digest = hashlib.sha256(json.dumps(source_before, sort_keys=True).encode()).hexdigest()
    try:
        commit = subprocess.check_output(["git", "rev-parse", "--verify", "HEAD"], cwd=ROOT,
                                         text=True, stderr=subprocess.DEVNULL).strip()
    except subprocess.CalledProcessError:
        commit = None
    receipt = {
        "project": project_before, "bridge": bridge_before,
        "started_at": stamp, "target": args.target, "project_commit": commit,
        "source_status": capture(["git", "status", "--porcelain"]),
        "source_inventory_sha256": before_digest,
        "lean_version": capture(["lean", "--version"]), "tools": pins,
        "tool_binary_sha256": {"comparator": digest(comparator), "lean4export": digest(exporter)},
        "trusted_boundary": boundary,
        "inputs": {name: digest(wrapper / name) for name in
                   ("Challenge.lean", "Solution.lean", "lakefile.toml", "config.json", "lean-toolchain")},
        "sandbox": "none: pinned upstream fake-landrun adapter; owned local sources",
        "nanoda": False, "status": "prepared", "exit_code": None,
    }
    result = wrapper / "result.json"
    result.write_text(json.dumps(receipt, indent=2) + "\n")
    print(f"Comparator directory: {wrapper}", flush=True)
    if args.prepare_only:
        print("Preparation finished; comparator has not run.", flush=True)
        return 0
    environment = os.environ.copy()
    environment.pop("LEAN_PATH", None)
    environment.update({"COMPARATOR_LEAN4EXPORT": str(exporter), "COMPARATOR_LANDRUN": str(landrun),
                        "LEAN_ABORT_ON_PANIC": "1"})
    environment.setdefault("LEAN_NUM_THREADS", "4")
    print("Running comparator without a sandbox; no nanoda check is requested.", flush=True)
    with (wrapper / "comparator.log").open("w") as out, (wrapper / "comparator.err").open("w") as err:
        process = subprocess.run(["lake", "env", str(comparator), "config.json"], cwd=wrapper,
                                 env=environment, stdout=out, stderr=err)
    verdict = (wrapper / "comparator.log").read_text().strip().splitlines()
    receipt.update({"finished_at": dt.datetime.now(dt.timezone.utc).isoformat(),
                    "exit_code": process.returncode,
                    "verdict": verdict[-1] if verdict else "",
                    "source_unchanged": (source_before == source_inventory()
                                         and identity(ROOT) == project_before)})
    try:
        receipt["boundary_after"] = verify_boundary()
        if args.target == "unconditional":
            receipt["bridge_after"] = bridge_evidence()
            if receipt["bridge_after"] != bridge_before:
                raise RuntimeError("Bridge inputs or build receipts changed during comparison.")
        boundary_ok = True
    except (RuntimeError, OSError, subprocess.CalledProcessError) as error:
        boundary_ok = False
        receipt["boundary_error"] = str(error)
    passed = (process.returncode == 0 and receipt["verdict"] == "Your solution is okay!"
              and receipt["source_unchanged"] and boundary_ok)
    receipt["status"] = "pass" if passed else "fail"
    receipt["log_sha256"] = digest(wrapper / "comparator.log")
    receipt["stderr_sha256"] = digest(wrapper / "comparator.err")
    result.write_text(json.dumps(receipt, indent=2) + "\n")
    if args.receipt_output:
        save_json(args.receipt_output, receipt)
    print(f"Comparator {receipt['status']}: {receipt['verdict']}", flush=True)
    print(f"Receipt: {result}", flush=True)
    return 0 if passed else (process.returncode or 1)


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (RuntimeError, OSError, subprocess.CalledProcessError) as error:
        print(f"Comparator setup failed: {error}", file=sys.stderr)
        raise SystemExit(2)
