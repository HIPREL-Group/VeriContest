"""Unit tests for the evaluator. Run: python3 -m unittest discover -s evaluation/tests"""
import os
import re
import subprocess
import sys
import tempfile
import unittest
from unittest import mock
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from vceval import checks, harness, spec_tests  # noqa: E402
from vceval.config import BENCH_ROOT, TASKS, VERUS_BIN  # noqa: E402
from vceval.extract import extract_program  # noqa: E402
from vceval.generate import build_prompt  # noqa: E402
from vceval.score import automatic_pass, needs_spec_review  # noqa: E402


class Extraction(unittest.TestCase):
    TEXT = "```rust\nfn helper() {}\n```\nthen\n```rust\nimpl Solution { }\n```\n```\nnotes\n```"

    def test_last_rule_prefers_last_solution_block(self):
        self.assertEqual(extract_program(self.TEXT, "last"), "impl Solution { }\n")

    def test_first_rule_takes_first_block(self):
        self.assertEqual(extract_program(self.TEXT, "first"), "fn helper() {}\n")

    def test_no_fence_uses_whole_response(self):
        self.assertEqual(extract_program("  impl Solution {}  ", "first"), "impl Solution {}\n")
        self.assertIsNone(extract_program("   ", "last"))


class Prompts(unittest.TestCase):
    def test_every_placeholder_is_filled(self):
        for key in TASKS:
            with self.subTest(task=key):
                for pid in ("leetcode/lc1", "codeforces/cf1006C"):
                    prompt = build_prompt(key, pid)
                    for placeholder in TASKS[key]["inputs"]:
                        self.assertNotIn("{{" + placeholder + "}}", prompt)
                    self.assertIn("# Input Field", prompt)


class OracleTemplates(unittest.TestCase):
    def test_in_place_drivers_serialize_after_the_call(self):
        for pid in ("lc73", "lc1089", "lc189", "lc26", "lc27", "lc280", "lc283", "lc289", "lc344", "lc75", "lc80", "lc88"):
            with self.subTest(problem=pid):
                d = BENCH_ROOT / "leetcode" / pid
                oracle = d / "tests" / "reference_oracle.rs"
                raw = oracle.read_text() if oracle.exists() else (d / "tests/harness.rs").read_text().replace(
                    (d / "code.rs").read_text(), harness.INCLUDE, 1)
                _, loaded = harness.template(d)
                # The released driver owns output serialization; loading does
                # not inject or duplicate a repair.
                self.assertIn("let _mut_", raw)
                self.assertEqual(raw, loaded)

    def test_helper_parameter_names_do_not_change_driver_types(self):
        for pid, names in {"lc3107": ["k"], "lc327": ["lower", "upper"],
                           "lc440": ["n", "k"], "lc600": ["n"]}.items():
            with self.subTest(problem=pid):
                _, loaded = harness.template(BENCH_ROOT / "leetcode" / pid)
                for name in names:
                    self.assertIn(f"let {name}: i32 = parse_number::<i32>", loaded)

    def test_camel_case_dataset_keys_remain_supported(self):
        _, text = harness.template(BENCH_ROOT / "leetcode" / "lc2960")
        self.assertIn("camel", text)


class Splicing(unittest.TestCase):
    def test_codegen_nl_always_uses_rustc(self):
        code = (BENCH_ROOT / "leetcode" / "lc1" / "code.rs").read_text()
        backend, src = harness.build_source(BENCH_ROOT / "leetcode" / "lc1", code, "rustc")
        self.assertEqual(backend, "rustc")
        self.assertNotIn('include!("../code.rs")', src)

    def test_codeforces_keeps_main_rs_and_replaces_impl(self):
        code = (BENCH_ROOT / "codeforces" / "cf1006C" / "code.rs").read_text()
        _, src = harness.build_source(BENCH_ROOT / "codeforces" / "cf1006C", code, "rustc")
        self.assertEqual(src.count("impl Solution"), 1)
        self.assertEqual(src.count("fn main"), 1)

    def test_driver_fns_redefined_by_the_program_are_dropped(self):
        # cf472B's main.rs repeats code.rs's free helpers; cf6A's main.rs has a
        # second impl Solution with a has_segment the reference also defines.
        for pid in ("codeforces/cf472B", "codeforces/cf6A"):
            with self.subTest(problem=pid):
                d = BENCH_ROOT / pid
                _, src = harness.build_source(d, (d / "verified.rs").read_text(), "auto")
                names = re.findall(r"\bfn\s+(\w+)", src)
                self.assertEqual(len(names), len(set(names)))
        _, src = harness.build_source(BENCH_ROOT / "codeforces" / "cf6A",
                                      (BENCH_ROOT / "codeforces" / "cf6A" / "code.rs").read_text(), "rustc")
        self.assertEqual(src.count("fn has_segment"), 1)

    def test_auto_policy_strips_nothing_from_verus_programs(self):
        code = (BENCH_ROOT / "leetcode" / "lc1" / "verified.rs").read_text()
        backend, src = harness.build_source(BENCH_ROOT / "leetcode" / "lc1", code, "auto")
        self.assertEqual(backend, "verus")
        self.assertIn("invariant", src)
        self.assertEqual(src.count("fn main"), 1)


@unittest.skipUnless(VERUS_BIN.is_file(), "bundled Verus not found")
class HarnessCompile(unittest.TestCase):
    # The drivers' rustc stand-ins for vstd's `set` / `unicode_len` must not
    # clash with vstd under Verus, and must still serve plain rustc.
    PIDS = ("leetcode/lc2022", "leetcode/lc2914")

    def compile(self, pid, filename, policy):
        d = BENCH_ROOT / pid
        backend, src = harness.build_source(d, (d / filename).read_text(), policy)
        with tempfile.TemporaryDirectory() as tmp:
            main, binary = Path(tmp) / "main.rs", Path(tmp) / "main"
            main.write_text(src)
            cmd = ([str(VERUS_BIN), "--no-verify", "--compile", str(main), "-o", str(binary)] if backend == "verus"
                   else [os.environ.get("VCEVAL_RUSTC", "rustc"), "--edition", "2021", str(main), "-o", str(binary)])
            return backend, subprocess.run(cmd, capture_output=True, text=True, timeout=120)

    def test_verus_programs_compile_with_vstd_methods(self):
        for pid in self.PIDS:
            with self.subTest(problem=pid):
                backend, cp = self.compile(pid, "verified.rs", "auto")
                self.assertEqual(backend, "verus")
                self.assertEqual(cp.returncode, 0, cp.stderr[-2000:])

    def test_plain_rust_still_gets_the_stand_ins(self):
        for pid in self.PIDS:
            with self.subTest(problem=pid):
                backend, cp = self.compile(pid, "code.rs", "rustc")
                self.assertEqual(backend, "rustc")
                self.assertEqual(cp.returncode, 0, cp.stderr[-2000:])


class SpecStub(unittest.TestCase):
    def test_exec_bodies_diverge_and_specs_stay(self):
        spec = (BENCH_ROOT / "leetcode" / "lc1" / "spec.rs").read_text()
        stubbed = checks.stub_exec_bodies(spec)
        self.assertIn("{ loop {} }", stubbed)
        self.assertIn("ensures", stubbed)

    def test_every_exec_fn_is_stubbed_spec_and_proof_fns_kept(self):
        code = ("impl NumArray {\n    pub fn new(nums: Vec<i32>) -> (result: Self)\n        ensures result.v@ == nums@,\n    {\n    }\n}\n"
                "impl Solution {\n    fn helper(v: &Vec<i32>) -> (bool, usize) {\n        let c = '{';\n    }\n"
                "    pub open spec fn f(n: int) -> int\n        decreases if n > 0 { n } else { 0 },\n    {\n        n\n    }\n"
                "    proof fn lemma() ensures f(0) == 0 {\n    }\n}\n")
        stubbed = checks.stub_exec_bodies(code)
        self.assertEqual(stubbed.count("{ loop {} }"), 2)
        self.assertIn("decreases if n > 0 { n } else { 0 },\n    {\n        n\n    }", stubbed)
        self.assertIn("ensures f(0) == 0 {\n    }", stubbed)

    @unittest.skipUnless(VERUS_BIN.is_file(), "bundled Verus not found")
    def test_reference_specs_typecheck(self):
        # Helper fns, `-> Self` constructors and non-Solution impls.
        for pid in ("leetcode/lc1007", "leetcode/lc303", "leetcode/lc1095", "codeforces/cf474B"):
            with self.subTest(problem=pid), tempfile.TemporaryDirectory() as tmp:
                spec = (BENCH_ROOT / pid / "spec.rs").read_text()
                self.assertEqual(checks.typecheck_spec(spec, Path(tmp))["status"], "pass")


class LynetteCompat(unittest.TestCase):
    def test_returns_becomes_an_ensures_conjunct(self):
        code = "fn f(c: i32) -> bool\n    requires\n        0 <= c,\n    returns\n        g(c as int),\n{\n    true\n}\n"
        out = checks.lynette_compatible(code)
        self.assertNotIn("    returns", out)
        self.assertIn("ensures __lynette_returns(g(c as int)),", out)
        self.assertIn("{\n    true\n}", out)

    def test_returns_merges_into_existing_ensures(self):
        code = "fn f(x: u64) -> (r: u64)\n    ensures\n        r > 0\n    returns\n        g(x),\n    decreases 0,\n{ x }\n"
        out = checks.lynette_compatible(code)
        self.assertEqual(out.count("ensures"), 1)
        self.assertIn("r > 0,\n__lynette_returns(g(x)),", out)
        self.assertIn("decreases 0,", out)

    def test_ensures_block_is_parenthesized(self):
        code = "proof fn l()\n    ensures\n    {\n        let a = 1;\n        a == 1\n    },\n{\n}\n"
        out = checks.lynette_compatible(code)
        self.assertIn("ensures\n    ({\n        let a = 1;\n        a == 1\n    }),", out)

    def test_other_code_is_unchanged(self):
        code = (BENCH_ROOT / "leetcode" / "lc1" / "verified.rs").read_text()
        self.assertEqual(checks.lynette_compatible(code), code)


LYNETTE = checks.lynette_path()


@unittest.skipUnless(LYNETTE, "lynette not built (evaluation/setup_tools.sh)")
class LynetteGate(unittest.TestCase):
    def preserved(self, original, candidate):
        with tempfile.TemporaryDirectory() as tmp:
            return checks.preserved(original, candidate, Path(tmp), LYNETTE)["status"]

    def test_golds_with_returns_and_ensures_blocks_pass(self):
        for pid in ("leetcode/lc633", "codeforces/cf688A", "leetcode/lc1526", "leetcode/lc3075"):
            with self.subTest(problem=pid):
                d = BENCH_ROOT / pid
                self.assertEqual(self.preserved((d / "code_spec.rs").read_text(), (d / "verified.rs").read_text()), "pass")

    def test_golds_with_proof_only_annotations_pass(self):
        # loop_isolation + spec `when`; spec `via`; `Ghost(..)` lets;
        # exec fn `decreases`; split `impl Solution`.
        for pid in ("codeforces/cf1840C", "leetcode/lc1837", "leetcode/lc1509",
                    "leetcode/lc912", "leetcode/lc2860"):
            with self.subTest(problem=pid):
                d = BENCH_ROOT / pid
                self.assertEqual(self.preserved((d / "code_spec.rs").read_text(), (d / "verified.rs").read_text()), "pass")

    def test_other_loop_attribute_is_rejected(self):
        d = BENCH_ROOT / "codeforces" / "cf1840C"
        gold = (d / "verified.rs").read_text()
        cheat = gold.replace("#[verifier::loop_isolation(false)]", "#[cfg(FALSE)]", 1)
        self.assertNotEqual(cheat, gold)
        self.assertEqual(self.preserved((d / "code_spec.rs").read_text(), cheat), "fail")

    def test_requires_only_where_another_fn_must_establish_it(self):
        orig = ("use vstd::prelude::*;\nverus! {\npub struct Solution;\nimpl Solution {\n"
                "    pub fn count(n: u32) -> (r: u32)\n        ensures r == n,\n        decreases n,\n"
                "    {\n        if n == 0 { 0 } else { Self::count(n - 1) + 1 }\n    }\n"
                "    pub fn entry(n: u32) -> (r: u32)\n        ensures r == n,\n    {\n        Self::helper(n)\n    }\n"
                "    fn helper(n: u32) -> u32 {\n        n\n    }\n}\n}\n")
        # Only its own recursive calls would have to establish this.
        recursive = orig.replace("        ensures r == n,\n        decreases n,",
                                 "        requires n == 0,\n        ensures r == n,\n        decreases n,")
        helper = orig.replace("    fn helper(n: u32) -> u32 {", "    fn helper(n: u32) -> u32\n        requires n < 100,\n    {")
        self.assertNotEqual(recursive, orig)
        self.assertNotEqual(helper, orig)
        self.assertEqual(self.preserved(orig, recursive), "fail")
        self.assertEqual(self.preserved(orig, helper), "pass")

    def test_redefined_spec_fn_is_rejected(self):
        d = BENCH_ROOT / "leetcode" / "lc633"
        gold = (d / "verified.rs").read_text()
        cheat = gold.replace("pub open spec fn judge_square_sum_spec(c: int) -> bool {",
                             "pub open spec fn judge_square_sum_spec(c: int) -> bool { true }\n"
                             "    pub open spec fn unused_spec(c: int) -> bool {", 1)
        self.assertNotEqual(cheat, gold)
        self.assertEqual(self.preserved((d / "code_spec.rs").read_text(), cheat), "fail")


def _phase(result="PASS", scored=10, unexpected=0, unparsed=0):
    return {"result": result, "scored": scored, "unexpected": unexpected, "unparsed": unparsed}


def _ran(pos=None, neg=None):
    return {"stage": "ran", "backend": "direct",
            "phases": {"positive": _phase(**(pos or {})), "negative": _phase(**{"scored": 20, **(neg or {})})}}


class SpecTestsPolicy(unittest.TestCase):
    """post2exe runs on the reference spec.rs first, then on the answer."""

    def verdict(self, answer, reference=None):
        with tempfile.TemporaryDirectory() as tmp, \
                mock.patch.object(spec_tests, "run_post2exe", side_effect=[reference or _ran(), answer]):
            return spec_tests.spec_tests("leetcode/lc1", "", Path("."), Path(tmp))

    def test_outcomes(self):
        self.assertEqual(self.verdict(_ran())["status"], "pass")
        self.assertEqual(self.verdict(_ran(pos={"result": "FAIL", "unexpected": 1}))["status"], "fail")
        self.assertEqual(self.verdict(_ran(pos={"scored": 9}))["status"], "fail")  # precondition too strong
        self.assertEqual(self.verdict(_ran(neg={"result": "FAIL", "unexpected": 3}))["status"], "fail")

    def test_human_review_reasons(self):
        cases = [
            ({"stage": "generate", "detail": "unbounded forall binder"}, "post2exe cannot handle it"),
            ({"stage": "compile", "detail": "error"}, "post2exe cannot handle it"),
            ({"stage": "timeout", "phase": "negative"}, "timeout"),
            (_ran(pos={"unparsed": 1}), "post2exe cannot handle it"),
        ]
        for run, reason in cases:
            with self.subTest(answer=run["stage"]):
                r = self.verdict(run)
                self.assertEqual((r["status"], r["review_reason"]), ("unsupported", reason))
            with self.subTest(reference=run["stage"]):  # the answer is never run
                r = self.verdict(None, reference=run)
                self.assertEqual((r["status"], r["review_reason"]), ("unsupported", reason))
        r = self.verdict(None, reference=_ran(neg={"result": "FAIL", "unexpected": 1}))
        self.assertEqual((r["status"], r["review_reason"]), ("unsupported", "post2exe cannot handle it"))


class Verdicts(unittest.TestCase):
    def test_end2end_needs_verus_tests_and_spec_tests(self):
        ok = {"verus": {"status": "pass"}, "code_tests": {"status": "pass"}, "spec_tests": {"status": "pass"}}
        self.assertTrue(automatic_pass("End2End", ok))
        self.assertFalse(automatic_pass("End2End", {**ok, "verus": {"status": "timeout"}}))
        self.assertFalse(automatic_pass("End2End", {**ok, "code_tests": {"status": "not_run"}}))
        self.assertFalse(automatic_pass("End2End", {**ok, "spec_tests": {"status": "fail"}}))

    def test_untestable_spec_goes_to_human_review(self):
        review = {"verus": {"status": "pass"}, "code_tests": {"status": "pass"},
                  "spec_tests": {"status": "unsupported", "review_reason": "post2exe timed out (positive)"}}
        self.assertFalse(automatic_pass("End2End", review))
        self.assertTrue(needs_spec_review("End2End", review))
        self.assertFalse(needs_spec_review("End2End", {**review, "code_tests": {"status": "fail"}}))
        self.assertTrue(needs_spec_review("SpecGen", {"spec_tests": {"status": "unsupported"}}))

    def test_specgen_needs_spec_tests(self):
        self.assertTrue(automatic_pass("SpecGen", {"spec_tests": {"status": "pass"}}))
        self.assertFalse(automatic_pass("SpecGen", {"spec_tests": {"status": "fail"}}))


if __name__ == "__main__":
    unittest.main()
