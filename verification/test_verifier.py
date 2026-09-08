#!/usr/bin/env python3
"""Regression checks for source-census and comparator cache boundaries."""

import importlib.util
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


if __name__ == "__main__":
    unittest.main()
