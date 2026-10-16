import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from vceval import checks


class OutputComparison(unittest.TestCase):
    def test_integers_are_exact_and_type_checked(self):
        for expected, actual in [(10**9, 10**9 + 1), (1, True), (0, False),
                                 (1, 1.0), (1, "1"), (2**100, 2**100 + 1)]:
            with self.subTest(expected=expected, actual=actual):
                self.assertFalse(checks._outputs_match(expected, actual))
        self.assertTrue(checks._outputs_match(2**100, 2**100))

    def test_booleans_are_not_truthiness_checks(self):
        for expected in (True, False):
            self.assertTrue(checks._outputs_match(expected, expected))
            for actual in (not expected, 0, 1, 42, "true", "", [], None):
                with self.subTest(expected=expected, actual=actual):
                    self.assertFalse(checks._outputs_match(expected, actual))

    def test_floats_keep_tolerance_but_reject_nonfinite_and_wrong_types(self):
        for expected, actual in [(1.0, 1), (1.0, 1.0000005), (0.0, 0.0000005),
                                 (-1000.0, -1000.0005)]:
            self.assertTrue(checks._outputs_match(expected, actual))
        for expected, actual in [(1.0, 1.001), (1.0, True), (1.0, "1"),
                                 (1.0, 10**1000), (1.0, float("nan")),
                                 (1.0, float("inf")), (float("inf"), float("inf")),
                                 (float("nan"), float("nan"))]:
            self.assertFalse(checks._outputs_match(expected, actual))

    def test_structures_apply_rules_recursively(self):
        expected = {"values": [10**9, True, {"average": 1.0}], "unused": None}
        self.assertTrue(checks._outputs_match(expected,
            {"unused": None, "values": [10**9, True, {"average": 1.0000005}]}))
        for values in ([10**9 + 1, True, {"average": 1.0}],
                       [10**9, 1, {"average": 1.0}],
                       [10**9, True], [True, 10**9, {"average": 1.0}]):
            self.assertFalse(checks._outputs_match(expected, {"values": values, "unused": None}))
        self.assertFalse(checks._outputs_match(expected, {**expected, "extra": 1}))
        self.assertFalse(checks._outputs_match([], {}))
        self.assertFalse(checks._outputs_match({"a": None}, {}))

    def test_strings_and_null_do_not_coerce(self):
        self.assertTrue(checks._outputs_match(" YES\n", "YES"))
        self.assertTrue(checks._outputs_match(None, None))
        for expected, actual in [("1", 1), ("True", True), ("None", None),
                                 (None, 0), ("a b", "ab")]:
            self.assertFalse(checks._outputs_match(expected, actual))

    def test_scorer_rejects_a_wrong_integer(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            cases = root / "leetcode/lc1/tests/testcases.jsonl"
            cases.parent.mkdir(parents=True)
            cases.write_text(json.dumps({"input": {}, "output": 10**9}) + "\n")
            outputs = [subprocess.CompletedProcess([], 0, "", ""),
                       subprocess.CompletedProcess([], 0, '{"output":1000000001}\n', "")]
            with patch.object(checks.harness, "build_source", return_value=("rustc", "")), \
                 patch.object(checks.harness, "template", return_value=("oracle", "")), \
                 patch.object(checks, "load_checker", return_value=None), \
                 patch.object(checks.subprocess, "run", side_effect=outputs):
                result = checks.code_tests("leetcode/lc1", "", "rustc", root, root)
            self.assertEqual(result["status"], "fail")
            self.assertEqual(result["passed"], 0)
            self.assertEqual(result["total"], 1)
