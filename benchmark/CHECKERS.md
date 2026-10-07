# Output Checkers

Some problems accept multiple feasible answers. When a problem provides
`tests/checker.py`, use it instead of comparing against one reference answer.
Inputs must satisfy the problem's preconditions; the checker judges outputs,
not input validity.

## Usage

From the repository root (Python 3.9+):

```bash
python3 benchmark/leetcode/lc905/tests/checker.py < candidate_outputs.jsonl
```

Each line contains `{"input": ..., "output": ...}`. The checker emits
`accept`, `reject`, or `error` per line. Read these verdicts: exit status 0
does not mean every answer passed. Malformed records cause exit status 2.
The Python API is `check(input, output) -> bool`.

- **LeetCode:** input is an object keyed by function parameters; output is the
  return value. For in-place functions, include the modified arguments and any
  return value in an output object.
- **Codeforces:** input and output are complete contest stdin/stdout strings.

Each checker's `CASES` examples show its exact record format.

## Development Tests

```bash
python3 benchmark/leetcode/lc905/tests/checker.py --self-test
python3 test_gen/test_checkers.py
```
