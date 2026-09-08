#!/usr/bin/env python3
"""Regression checks for source-census and comparator cache boundaries."""

import importlib.util
import json
import os
import subprocess
import sys
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch


PROJECT = Path(__file__).resolve().parents[1]


def load(name, relative):
    spec = importlib.util.spec_from_file_location(name, PROJECT / relative)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


scanner = load("source_scan", "verification/scan.py")
runner = load("comparator_run", "verification/comparator/run.py")
bridge = load("bridge_run", "verification/unconditional/tools/bridge.py")
suite = load("verification_check", "verification/check.py")
evidence = load("verification_evidence", "verification/evidence.py")


class SourceCensusTests(unittest.TestCase):
    def test_quoted_additional_axiom_is_counted_and_rejected(self):
        source = "axiom firstBoundary : Prop\naxiom \u00absecondBoundary\u00bb : Prop\n"
        declarations = scanner.axiom_declarations(scanner.code_only(source))
        self.assertEqual(len(declarations), 2)
        self.assertEqual(declarations[0]["name"], "firstBoundary")
        self.assertIsNone(declarations[1]["name"])

    def test_comments_strings_and_quoted_identifiers_are_not_keywords(self):
        source = '-- axiom fake\n/- axiom outer /- axiom inner -/ -/\n"axiom string"\n\u00abaxiom\u00bb\naxiom firstBoundary : Prop'
        declarations = scanner.axiom_declarations(scanner.code_only(source))
        self.assertEqual([item["name"] for item in declarations], ["firstBoundary"])


class CacheBoundaryTests(unittest.TestCase):
    def setUp(self):
        temp_parent = PROJECT / ".verify-work/tests"
        temp_parent.mkdir(parents=True, exist_ok=True)
        self.temporary = tempfile.TemporaryDirectory(dir=temp_parent)
        self.addCleanup(self.temporary.cleanup)
        self.base = Path(self.temporary.name)
        self.project = self.base / "project"
        self.project.mkdir()
        self.external = self.base / "external"
        self.external.mkdir()

    def test_external_top_level_cache_prefix_is_rejected(self):
        entry = self.project / "Prefix"
        entry.symlink_to(self.external, target_is_directory=True)
        with patch.object(runner, "ROOT", self.project):
            with self.assertRaisesRegex(RuntimeError, "outside"):
                runner.validate_cache_tree(entry)

    def test_external_nested_cache_link_is_rejected(self):
        entry = self.project / "Prefix"
        entry.mkdir()
        target = self.external / "Module.olean"
        target.touch()
        (entry / "Module.olean").symlink_to(target)
        with patch.object(runner, "ROOT", self.project):
            with self.assertRaisesRegex(RuntimeError, "outside"):
                runner.validate_cache_tree(entry)

    def test_internal_cache_links_are_accepted(self):
        entry = self.project / "Prefix"
        entry.mkdir()
        target = self.project / "Module.olean"
        target.touch()
        (entry / "Module.olean").symlink_to(target)
        with patch.object(runner, "ROOT", self.project):
            runner.validate_cache_tree(entry)


class BridgeTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.project = self.root / "project"
        self.upstream = self.project / "upstream/3d-sticky-kakeya"
        self.packages = self.project / ".lake/packages"
        self.state = self.project / "verification/unconditional/.bridge"
        self.lib = self.state / "build/lib/lean"
        self.core = self.project / ".lake/build/lib/lean"
        self.core.mkdir(parents=True)
        self.upstream.mkdir(parents=True)
        self.packages.mkdir(parents=True)
        self.compiler = self.root / "lean/bin/lean"
        self.compiler.parent.mkdir(parents=True)
        self.compiler.write_text("fixture compiler")
        self.config = {"numina": str(self.project), "bytedance": str(self.upstream),
                       "packages": str(self.packages), "lean": str(self.compiler)}
        for target, value in (("STATE", self.state), ("LIB", self.lib),
                              ("OVERLAY", self.state / "compatibility"), ("PACKAGES", [])):
            context = patch.object(bridge, target, value)
            context.start()
            self.addCleanup(context.stop)
        (self.project / "lake-manifest.json").write_bytes(
            (PROJECT / "lake-manifest.json").read_bytes())
        (self.project / "lean-toolchain").write_text(bridge.LOCK["toolchain"] + "\n")
        (self.core / "Kakeya.olean").write_text("conditional root")

    def test_public_layout_accepts_current_project_commit_and_records_it(self):
        def git(path, *args):
            if args == ("status", "--porcelain"):
                return ""
            return bridge.LOCK["bytedance_commit"]
        current = {"commit": "new-project-commit", "status": "", "source_sha256": "source"}
        def compiler(command, **kwargs):
            return bridge.LOCK["lean_githash"] if command[-1] == "--githash" else "Lean 4.32.0-rc1"
        with patch.object(bridge, "git", side_effect=git), \
                patch.object(bridge, "identity", return_value=current), \
                patch.object(bridge.subprocess, "check_output", side_effect=compiler), \
                patch.object(bridge, "overlays"), \
                patch.object(sys, "argv", ["bridge.py", "configure", "--numina", str(self.project),
                                          "--bytedance", str(self.upstream), "--packages", str(self.packages),
                                          "--lean", str(self.compiler)]):
            self.assertEqual(bridge.main(), 0)
        recorded = json.loads((self.state / "input-identities.json").read_text())
        self.assertEqual(recorded["numina"], current)

    def test_wrong_upstream_revision_is_rejected(self):
        with patch.object(bridge, "identity", return_value={}), \
                patch.object(bridge, "git", return_value="wrong-commit"):
            with self.assertRaisesRegex(RuntimeError, "clean checkout"):
                bridge.verify_inputs(self.config)

    def test_wrong_compiler_revision_is_rejected(self):
        def git(path, *args):
            return "" if args == ("status", "--porcelain") else bridge.LOCK["bytedance_commit"]
        with patch.object(bridge, "identity", return_value={}), \
                patch.object(bridge, "git", side_effect=git), \
                patch.object(bridge.subprocess, "check_output", return_value="4.32.0-rc1 wrong revision"):
            with self.assertRaisesRegex(RuntimeError, "Wrong Lean compiler"):
                bridge.verify_inputs(self.config)

    def test_unconditional_namespace_and_comment_imports(self):
        path = self.project / "Unconditional/Test.lean"
        path.parent.mkdir()
        path.write_text("/- import Unconditional.DoesNotExist -/\nimport Unconditional.Child\nimport Kakeya.Base\n")
        (path.parent / "Child.lean").write_text("-- import Unconditional.Missing\n")
        self.assertEqual(bridge.closure(self.config, ["Unconditional.Test"]),
                         {"Unconditional.Test": {"Unconditional.Child"}, "Unconditional.Child": set()})

    def test_unlisted_overlay_cannot_replace_pinned_source(self):
        module = "MyLeanRepo.Example"
        shadow = bridge.OVERLAY / "MyLeanRepo/Example.lean"
        shadow.parent.mkdir(parents=True)
        shadow.write_text("def changed := True\n")
        selected, base = bridge.source(self.config, module)
        self.assertEqual(selected, self.upstream / "MyLeanRepo/Example.lean")
        self.assertEqual(base, self.upstream)

    def test_external_kakeya_and_private_fragment_invalidate_receipt(self):
        path = self.project / "Unconditional/Test.lean"
        path.parent.mkdir()
        path.write_text("import Kakeya.Base\n")
        (self.core / "Kakeya").mkdir()
        (self.core / "Kakeya/Base.olean").write_text("public")
        private = self.core / "Kakeya/Base.olean.private"
        private.write_text("first private")
        (self.core / "Init.olean").write_text("Init")
        first = bridge.inputs(self.config, "Unconditional.Test")
        self.assertIn("Kakeya.Base", first["dependencies"])
        private.write_text("changed private")
        self.assertNotEqual(first, bridge.inputs(self.config, "Unconditional.Test"))


class OrchestrationTests(unittest.TestCase):
    def test_full_suite_contains_both_proofs_and_both_comparators(self):
        checks = suite.stages("full", Path("upstream"), 2)
        self.assertEqual([name for name, _ in checks],
                         ["regressions", "core", "unconditional", "comparator-conditional", "comparator-unconditional"])
        self.assertEqual([name for name, _ in suite.stages("core", Path("upstream"), 2)],
                         ["regressions", "core"])

    def test_stage_failure_stops_suite_and_keeps_log_and_receipt(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)
            receipt = {"status": "running", "stages": []}
            checks = [("failure", [sys.executable, "-c", "print('failure detail'); raise SystemExit(7)"]),
                      ("must-not-run", ["missing-command"])]
            with self.assertRaisesRegex(RuntimeError, "exit code 7"):
                suite.execute(checks, output, receipt)
            saved = json.loads((output / "result.json").read_text())
            self.assertEqual(len(saved["stages"]), 1)
            self.assertEqual(saved["stages"][0]["status"], "fail")
            self.assertIn("failure detail", (output / "failure.log").read_text())
            self.assertEqual(saved["stages"][0]["log_sha256"], evidence.digest(output / "failure.log"))

    def test_aggregate_receipt_rejects_source_drift_after_passing_stages(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            with patch.object(suite, "ROOT", root), \
                    patch.object(suite, "identity", side_effect=[{"status": "", "source_sha256": "before"},
                                                                {"status": "", "source_sha256": "after"}]), \
                    patch.object(suite, "capture", return_value="fixture compiler"), \
                    patch.object(suite, "execute"), \
                    patch.object(sys, "argv", ["check.py", "--scope", "core"]):
                self.assertEqual(suite.main(), 1)
            receipt = json.loads(next((root / ".verification-results").glob("*/result.json")).read_text())
            self.assertEqual(receipt["status"], "fail")
            self.assertIn("sources changed", receipt["error"])

    def test_release_check_rejects_dirty_checkout_before_running_stages(self):
        with tempfile.TemporaryDirectory() as directory:
            with patch.object(suite, "ROOT", Path(directory)), \
                    patch.object(suite, "identity", return_value={"status": " M Example.lean"}), \
                    patch.object(suite, "execute") as execute, \
                    patch.object(sys, "argv", ["check.py", "--scope", "core", "--require-clean"]):
                self.assertEqual(suite.main(), 1)
                execute.assert_not_called()

    def test_source_identity_detects_uncommitted_edits(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            subprocess.run(["git", "init", "-q", str(root)], check=True)
            source = root / "Example.lean"
            source.write_text("def value := 1\n")
            subprocess.run(["git", "-C", str(root), "add", "."], check=True)
            subprocess.run(["git", "-C", str(root), "-c", "user.name=Test", "-c", "user.email=test@example.invalid",
                            "-c", "commit.gpgsign=false", "commit", "-qm", "Fixture"], check=True)
            before = evidence.identity(root)
            source.write_text("def value := 2\n")
            after = evidence.identity(root)
            self.assertEqual(before["commit"], after["commit"])
            self.assertNotEqual(before["source_sha256"], after["source_sha256"])
            self.assertTrue(after["status"])

    def test_unconditional_challenge_imports_only_mathlib(self):
        challenge = PROJECT / "verification/comparator/ChallengeUnconditional.lean.in"
        clean = scanner.code_only(challenge.read_text())
        imports = [name for line in bridge.IMPORT.findall(clean) for name in line.split()]
        self.assertTrue(imports)
        self.assertTrue(all(name.startswith("Mathlib.") for name in imports))
        config = json.loads((PROJECT / "verification/comparator/config-unconditional.json").read_text())
        self.assertIn("KakeyaDimensionThree_of_pureWZ2", json.dumps(config))

    def test_bridge_shell_selects_toolchain_from_project_directory(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            binary = root / "bin"
            binary.mkdir()
            log = root / "lean-cwd.txt"
            (binary / "lean").write_text('#!/bin/sh\npwd > "$CALL_LOG"\necho /fixture/toolchain\n')
            (binary / "python3").write_text("#!/bin/sh\nexit 0\n")
            for path in binary.iterdir():
                path.chmod(0o755)
            env = dict(os.environ, PATH=str(binary) + os.pathsep + os.environ["PATH"], CALL_LOG=str(log))
            result = subprocess.run(["bash", str(PROJECT / "verification/unconditional/run.sh"),
                                     "--upstream", str(root)], cwd=root, env=env, capture_output=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(Path(log.read_text().strip()), PROJECT)

    def test_bridge_shell_rejects_missing_and_invalid_job_values(self):
        script = PROJECT / "verification/unconditional/run.sh"
        for args in (["-j"], ["--upstream"], ["-j", "0"], ["-j", "-1"]):
            result = subprocess.run(["bash", str(script), *args], cwd="/tmp", capture_output=True)
            self.assertEqual(result.returncode, 2, result.stderr)


if __name__ == "__main__":
    unittest.main()
