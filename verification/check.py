#!/usr/bin/env python3
"""Run the core or full verification suite and retain a receipt, including failures."""

import argparse
import datetime as dt
import os
from pathlib import Path
import platform
import resource
import shutil
import subprocess
import sys
import time

from evidence import capture, digest, identity, save_json

ROOT = Path(__file__).resolve().parents[1]


def stages(scope, upstream, jobs):
    checks = [
        ("regressions", [sys.executable, "verification/test_verifier.py"]),
        ("core", ["bash", "verification/run.sh"]),
    ]
    if scope == "full":
        checks += [
            ("unconditional", ["bash", "verification/unconditional/run.sh",
                               "--upstream", str(upstream), "-j", str(jobs)]),
            ("comparator-conditional", [sys.executable, "verification/comparator/run.py",
                                       "--target", "conditional"]),
            ("comparator-unconditional", [sys.executable, "verification/comparator/run.py",
                                         "--target", "unconditional", "--jobs", str(jobs)]),
        ]
    return checks


def execute(checks, output, receipt):
    for name, command in checks:
        if name.startswith("comparator-"):
            command = [*command, "--receipt-output", str(output / (name + ".json"))]
        log = output / (name + ".log")
        stage = {"name": name, "command": command, "status": "running"}
        receipt["stages"].append(stage)
        save_json(output / "result.json", receipt)
        started = time.monotonic()
        print(f"Running {name}; log: {log}", flush=True)
        with log.open("w", encoding="utf-8") as stream:
            result = subprocess.run(command, cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT)
        stage.update({"exit_code": result.returncode,
                      "seconds": round(time.monotonic() - started, 2),
                      "status": "pass" if result.returncode == 0 else "fail",
                      "log_sha256": digest(log)})
        save_json(output / "result.json", receipt)
        if result.returncode:
            raise RuntimeError(f"{name} failed with exit code {result.returncode}; see {log}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--scope", choices=("core", "full"), default="full")
    parser.add_argument("--upstream", type=Path, default=ROOT / "upstream/3d-sticky-kakeya")
    parser.add_argument("--jobs", type=int, default=2, help="Concurrent bridge compiler processes")
    parser.add_argument("--require-clean", action="store_true",
                        help="Require a committed project snapshot for release evidence")
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    upstream = args.upstream.resolve()
    stamp = dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%S.%fZ")
    output = ROOT / ".verification-results" / stamp
    output.mkdir(parents=True)
    receipt = {"schema_version": 1, "scope": args.scope, "status": "running",
               "started_at": stamp, "stages": [], "bridge_jobs": args.jobs,
               "environment": {"platform": platform.platform(), "python": platform.python_version(),
                               "logical_cpus": os.cpu_count(),
                               "physical_memory_bytes": os.sysconf("SC_PAGE_SIZE") * os.sysconf("SC_PHYS_PAGES"),
                               "free_disk_bytes_before": shutil.disk_usage(ROOT).free},
               "cache_policy": "Local incremental artifacts; pinned dependency cache allowed"}
    save_json(output / "result.json", receipt)
    started = time.monotonic()
    try:
        receipt["project"] = identity(ROOT)
        if args.require_clean and receipt["project"]["status"]:
            raise RuntimeError("Release verification requires a clean, committed project checkout.")
        if args.scope == "full":
            receipt["upstream"] = identity(upstream)
        receipt["environment"]["lean"] = capture(ROOT, "lean", "--version")
        receipt["environment"]["lean_githash"] = capture(ROOT, "lean", "--githash")
        execute(stages(args.scope, upstream, args.jobs), output, receipt)
        receipt["project_after"] = identity(ROOT)
        if receipt["project_after"] != receipt["project"]:
            raise RuntimeError("Project sources changed during verification.")
        if args.scope == "full":
            receipt["upstream_after"] = identity(upstream)
            if receipt["upstream_after"] != receipt["upstream"]:
                raise RuntimeError("Upstream sources changed during verification.")
        receipt["status"] = "pass"
    except (RuntimeError, OSError, subprocess.CalledProcessError, KeyboardInterrupt) as error:
        receipt["status"] = "fail"
        receipt["error"] = str(error) or type(error).__name__
        print(receipt["error"], file=sys.stderr)
    finally:
        receipt.update({"finished_at": dt.datetime.now(dt.timezone.utc).isoformat(),
                        "seconds": round(time.monotonic() - started, 2),
                        "largest_child_peak_rss_kib": resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
                        "free_disk_bytes_after": shutil.disk_usage(ROOT).free})
        save_json(output / "result.json", receipt)
        print(f"{args.scope} verification {receipt['status']}: {output / 'result.json'}", flush=True)
    return 0 if receipt["status"] == "pass" else 1


if __name__ == "__main__":
    raise SystemExit(main())
