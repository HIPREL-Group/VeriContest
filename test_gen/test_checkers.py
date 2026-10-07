"""Regression tests for standalone problem checkers; no Post2Exe dependency."""

import ast
from collections import deque
import importlib.util
from itertools import permutations, product
import json
from pathlib import Path
import random
import re
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1] / "benchmark"
sys.dont_write_bytecode = True


def problem_dir(pid):
    return ROOT / ("leetcode" if pid.startswith("lc") else "codeforces") / pid


def load(pid):
    path = problem_dir(pid) / "tests" / "checker.py"
    spec = importlib.util.spec_from_file_location(pid, path)
    module = importlib.util.module_from_spec(spec)
    old = sys.argv
    try:
        sys.argv = [str(path), "--self-test"]
        spec.loader.exec_module(module)
    finally:
        sys.argv = old
    return module


def rust_value(value):
    if type(value) is int:
        return str(value)
    if isinstance(value, list):
        return "vec![" + ",".join(map(rust_value, value)) + "]"
    if isinstance(value, str) and len(value) == 1:
        return json.dumps(value) + ".chars().next().unwrap()"
    raise ValueError(value)


def lc_driver(pid, cases):
    source = problem_dir(pid) / "code.rs"
    signatures = list(re.finditer(r"pub fn (\w+)\s*\((.*?)\)\s*(?:->\s*([^\{]+))?\{", source.read_text(), re.S))
    signature = signatures[-1]
    function, args, result = signature.groups()
    params = [tuple(part.strip().split(":", 1)) for part in args.split(",") if part.strip()]
    chunks = [f"struct Solution;\ninclude!({json.dumps(str(source))});\nfn main() {{"]
    observed = []
    for data in cases:
        chunks.append("{")
        expressions, mutable = [], []
        for name, ty in params:
            if "CustomFunction" in ty:
                # The lc1237 fixture is the full monotone grid f(x,y)=x+y.
                value = "CustomFunction { values: (0..1001).map(|x| (0..1001).map(|y| x+y).collect()).collect() }"
            else:
                value = rust_value(data[name])
            chunks.append(f"let mut {name}: {ty.replace('&mut ', '').replace('&', '').strip()} = {value};")
            expressions.append(("&mut " if "&mut" in ty else "&" if "&" in ty else "") + name)
            if "&mut" in ty:
                mutable.append(name)
        chunks.append(f"let answer = Solution::{function}({', '.join(expressions)});")
        fields = []
        if result:
            chunks.append('println!("{:?}", answer);')
            fields.append("return")
        for name in mutable:
            chunks.append(f'println!("{{:?}}", {name});')
            fields.append(name)
        chunks.append("}")
        observed.append((fields, bool(mutable)))
    chunks.append("}")
    return "\n".join(chunks), observed


class ProblemCheckers(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        paths = sorted(ROOT.glob("*/*/tests/checker.py"))
        cls.modules = {p.parent.parent.name: load(p.parent.parent.name) for p in paths}

    def test_all_self_tests_and_jsonl(self):
        self.assertEqual(len(self.modules), 80)
        for pid, module in self.modules.items():
            with self.subTest(problem=pid):
                path = problem_dir(pid) / "tests" / "checker.py"
                run = subprocess.run([sys.executable, str(path), "--self-test"], text=True, capture_output=True, timeout=30)
                self.assertEqual(run.returncode, 0, run.stderr)
                data, output, _ = module.CASES[0]
                payload = json.dumps({"input": data, "output": output}) + '\n{"bad": 1}\n'
                run = subprocess.run([sys.executable, str(path)], input=payload, text=True, capture_output=True, timeout=30)
                self.assertEqual(run.returncode, 2, run.stderr)
                self.assertEqual(run.stdout.splitlines(), ["accept", "error"])

    def test_reference_programs(self):
        with tempfile.TemporaryDirectory(prefix="problem-checkers-") as directory:
            scratch = Path(directory)
            for pid, module in self.modules.items():
                with self.subTest(problem=pid):
                    binary = scratch / pid
                    if pid.startswith("cf"):
                        source = problem_dir(pid) / "main.rs"
                        cases = list(dict.fromkeys(data for data, _, _ in module.CASES))
                    else:
                        cases = [data for data, _, _ in module.CASES]
                        code, observed = lc_driver(pid, cases)
                        source = scratch / f"{pid}.rs"
                        source.write_text(code)
                    build = subprocess.run(["rustc", "--edition=2021", "-Awarnings", "-O", str(source), "-o", str(binary)],
                                           text=True, capture_output=True, timeout=60)
                    self.assertEqual(build.returncode, 0, build.stderr)
                    if pid.startswith("cf"):
                        for data in cases:
                            run = subprocess.run([str(binary)], input=data + "\n", text=True, capture_output=True, timeout=10)
                            self.assertEqual(run.returncode, 0, (pid, data, run.stderr))
                            self.assertTrue(module.check(data, run.stdout), (pid, data, run.stdout))
                    else:
                        run = subprocess.run([str(binary)], text=True, capture_output=True, timeout=30)
                        self.assertEqual(run.returncode, 0, run.stderr)
                        lines = iter(run.stdout.splitlines())
                        for data, (fields, mutable) in zip(cases, observed):
                            values = {key: ast.literal_eval(next(lines)) for key in fields}
                            output = values if mutable else values["return"]
                            self.assertTrue(module.check(data, output), (pid, output))
                        self.assertEqual(list(lines), [])

    def test_digit_coloring_exhaustive(self):
        module = self.modules["cf1209C"]
        for n in range(1, 6):
            for digits in product("012", repeat=n):
                digits = "".join(digits)
                possible = False
                data = f"1\n{n}\n{digits}"
                for colors in product("12", repeat=n):
                    colors = "".join(colors)
                    merged = [v for v, c in zip(digits, colors) if c == "1"] + [v for v, c in zip(digits, colors) if c == "2"]
                    expected = merged == sorted(merged)
                    possible |= expected
                    self.assertEqual(module.check(data, colors), expected, (digits, colors))
                self.assertEqual(module.check(data, "-"), not possible, digits)

    def test_contest_selection_exhaustive(self):
        module = self.modules["cf1708C"]
        for n in range(1, 6):
            for values in product(range(1, 4), repeat=n):
                for initial in (1, 2, 3):
                    feasible = []
                    for bits in product("01", repeat=n):
                        iq = initial
                        for value, bit in zip(values, bits):
                            if bit == "1":
                                if iq == 0:
                                    break
                                iq -= value > iq
                        else:
                            feasible.append("".join(bits))
                    maximum = max(s.count("1") for s in feasible)
                    winners = {s for s in feasible if s.count("1") == maximum}
                    data = f"1\n{n} {initial}\n" + " ".join(map(str, values))
                    for bits in product("01", repeat=n):
                        bits = "".join(bits)
                        self.assertEqual(module.check(data, bits), bits in winners, (values, initial, bits))

    def test_skip_optimality_exhaustive(self):
        module = self.modules["cf1279B"]
        for n in range(1, 6):
            for values in product((1, 2, 3), repeat=n):
                for budget in range(1, 10):
                    scores = []
                    for skip in range(n + 1):
                        remaining = [v for i, v in enumerate(values, 1) if i != skip]
                        spent = count = 0
                        for v in remaining:
                            if spent + v > budget:
                                break
                            spent += v
                            count += 1
                        scores.append(count)
                    data = f"1\n{n} {budget}\n" + " ".join(map(str, values))
                    for skip in range(n + 1):
                        expected = scores[skip] == max(scores) and (sum(values) > budget or skip == 0)
                        self.assertEqual(module.check(data, str(skip)), expected, (values, budget, skip))

    def test_permutations_exhaustive(self):
        for n in range(2, 8):
            candidates = list(permutations(range(1, n + 1)))
            optimum = max(min(abs(x-y) for x, y in zip(p, p[1:])) for p in candidates)
            for p in candidates:
                good = all(2 * p[k] != p[i] + p[j] for i in range(n) for k in range(i + 1, n) for j in range(k + 1, n))
                self.assertEqual(self.modules["lc932"].check({"n": n}, list(p)), good)
                expected = min(abs(x-y) for x, y in zip(p, p[1:])) == optimum
                self.assertEqual(self.modules["cf1754B"].check(f"1\n{n}", " ".join(map(str, p))), expected)

    def test_random_shifts_and_index_pairs(self):
        rng = random.Random(2026)
        def inversions(values):
            return sum(x > y for i, x in enumerate(values) for y in values[i + 1:])
        for _ in range(150):
            values = [rng.randint(1, 5) for _ in range(rng.randint(1, 8))]
            n = len(values)
            scores = {(l, r): inversions(values[:l] + values[l+1:r+1] + [values[l]] + values[r+1:])
                      for l in range(n) for r in range(l, n)}
            data = f"1\n{n}\n" + " ".join(map(str, values))
            for (l, r), score in scores.items():
                self.assertEqual(self.modules["cf2072D"].check(data, f"{l+1} {r+1}"), score == min(scores.values()))
            gap, diff = rng.randrange(n + 2), rng.randrange(7)
            valid = {(i, j) for i in range(n) for j in range(n) if abs(i-j) >= gap and abs(values[i]-values[j]) >= diff}
            args = {"nums": values, "index_difference": gap, "value_difference": diff}
            for pid in ("lc2903", "lc2905"):
                self.assertEqual(self.modules[pid].check(args, [-1, -1]), not valid)
                for i in range(n):
                    for j in range(n):
                        self.assertEqual(self.modules[pid].check(args, [i, j]), (i, j) in valid)

    def test_binary_filling_by_reversal_bfs(self):
        for n in range(1, 7):
            distances = {"0" * k + "1" * (n-k): 0 for k in range(n + 1)}
            queue = deque(distances)
            while queue:
                value = queue.popleft()
                for l in range(n):
                    for r in range(l+1, n+1):
                        other = value[:l] + value[l:r][::-1] + value[r:]
                        if other not in distances:
                            distances[other] = distances[value] + 1
                            queue.append(other)
            for pattern in product("01?", repeat=n):
                pattern = "".join(pattern)
                matches = [s for s in distances if all(p == "?" or p == c for p, c in zip(pattern, s))]
                optimum = min(distances[s] for s in matches)
                for s in matches:
                    self.assertEqual(self.modules["cf1837C"].check("1\n" + pattern, s), distances[s] == optimum)

    def test_impossibility_claims_against_enumeration(self):
        for n in range(2, 5):
            for values in product(range(1, 5), repeat=n):
                data = f"1\n{n}\n" + " ".join(map(str, values))
                divisors = {d for d in range(1, max(values) + 1)
                            if all((x % d == 0) != (y % d == 0) for x, y in zip(values, values[1:]))}
                self.assertEqual(self.modules["cf1618C"].check(data, "0"), not divisors)
                for d in range(1, 7):
                    self.assertEqual(self.modules["cf1618C"].check(data, str(d)), d in divisors)
                xs = {x for x in range(max(values) + 1)
                      if all(abs(v-x) <= abs(w-x) for v, w in zip(values, values[1:]))}
                self.assertEqual(self.modules["cf1772D"].check(data, "-1"), not xs)
        from math import gcd
        for n in range(1, 5):
            for low in range(1, 6):
                for high in range(low, 7):
                    possible = any(len({gcd(i, v) for i, v in enumerate(values, 1)}) == n
                                   for values in product(range(low, high + 1), repeat=n))
                    self.assertEqual(self.modules["cf1708B"].check(f"1\n{n} {low} {high}", "NO"), not possible)
        for low in range(1, 25):
            for high in range(low, 25):
                possible = any(gcd(x, total-x) > 1 for total in range(low, high+1) for x in range(1, total))
                self.assertEqual(self.modules["cf1872C"].check(f"1\n{low} {high}", "-1"), not possible)

    def test_operation_replay(self):
        rng = random.Random(1750)
        module = self.modules["cf1750C"]
        for _ in range(1000):
            n = rng.randrange(2, 7)
            first = [rng.randrange(2) for _ in range(n)]
            second = [rng.randrange(2) for _ in range(n)]
            aa, bb = first[:], second[:]
            ops = []
            for _ in range(rng.randrange(n + 6)):
                l = rng.randrange(n)
                r = rng.randrange(l, n)
                ops.append((l+1, r+1))
                for i in range(n):
                    if l <= i <= r:
                        aa[i] ^= 1
                    else:
                        bb[i] ^= 1
            data = f"1\n{n}\n" + "".join(map(str, first)) + "\n" + "".join(map(str, second))
            output = f"YES {len(ops)}\n" + "\n".join(f"{l} {r}" for l, r in ops)
            self.assertEqual(module.check(data, output), not any(aa + bb))

    def test_subarray_game_and_schedule_optimality(self):
        module = self.modules["cf1355D"]
        for n in range(1, 5):
            for values in product(range(1, 5), repeat=n):
                total = sum(values)
                sums = {sum(values[l:r]) for l in range(n) for r in range(l+1, n+1)}
                for target in range(total + 1):
                    output = "YES " + " ".join(map(str, values)) + f" {target}"
                    self.assertEqual(module.check(f"{n} {total}", output), target not in sums and total-target not in sums)
        module = self.modules["cf732B"]
        for original in product(range(3), repeat=3):
            for k in range(1, 5):
                candidates = [values for values in product(range(k+3), repeat=3)
                              if all(v >= old for v, old in zip(values, original))
                              and all(x+y >= k for x, y in zip(values, values[1:]))]
                optimum = min(sum(v)-sum(original) for v in candidates)
                data = f"3 {k}\n" + " ".join(map(str, original))
                for values in candidates:
                    extra = sum(values)-sum(original)
                    output = str(extra) + "\n" + " ".join(map(str, values))
                    self.assertEqual(module.check(data, output), extra == optimum)

    def test_tree_decompositions_by_edge_partition(self):
        rng = random.Random(981)
        module = self.modules["cf981C"]
        for _ in range(60):
            n = rng.randrange(2, 8)
            edges = [(i, rng.randrange(i)) for i in range(1, n)]
            graph = [[] for _ in range(n)]
            for i, (u, v) in enumerate(edges):
                graph[u].append((v, i))
                graph[v].append((u, i))
            paths = []
            for start in range(n):
                stack = [(start, -1, {start}, set())]
                while stack:
                    end, parent, vertices, used = stack.pop()
                    if start < end:
                        paths.append((start, end, vertices, used))
                    for v, edge in graph[end]:
                        if v != parent:
                            stack.append((v, end, vertices | {v}, used | {edge}))
            data = str(n) + "\n" + "\n".join(f"{u+1} {v+1}" for u, v in edges)
            for _ in range(80):
                chosen = [rng.choice(paths) for _ in range(rng.randrange(1, n))]
                output = f"YES {len(chosen)}\n" + "\n".join(f"{u+1} {v+1}" for u, v, _, _ in chosen)
                counts = [sum(i in path[3] for path in chosen) for i in range(n-1)]
                expected = (all(c == 1 for c in counts)
                            and all(x[2] & y[2] for x in chosen for y in chosen))
                self.assertEqual(module.check(data, output), expected, (data, output))


if __name__ == "__main__":
    unittest.main(verbosity=2)
