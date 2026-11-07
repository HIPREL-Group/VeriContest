# Range Addition II

You are given an `m x n` matrix `M` initialized with all `0`s and an array of operations `ops`, where `ops[i] = [ai, bi]` means `M[x][y]` should be incremented by 1 for all `0 <= x < ai` and `0 <= y < bi`.

Count and return the number of maximum integers in the matrix after performing all the operations.

## Example 1:

> **Input:** m = 3, n = 3, ops = [[2,2],[3,3]]
> **Output:** 4
> **Explanation:** The maximum integer in M is 2, and there are four of it in M.

## Example 2:

> **Input:** m = 3, n = 3, ops = [[2,2],[3,3],[3,3],[3,3],[2,2],[3,3],[3,3],[3,3],[2,2],[3,3],[3,3],[3,3]]
> **Output:** 4

## Example 3:

> **Input:** m = 3, n = 3, ops = []
> **Output:** 9

## Constraints:

- `1 <= m, n <= 4 * 10^4`
- `0 <= ops.length <= 10^4`
- `ops[i].length == 2`
- `1 <= ai <= m`
- `1 <= bi <= n`

## Starter Code

```dafny
predicate max_count_pre(m: int, n: int, ops: seq<seq<int>>)

predicate max_count_post(m: int, n: int, ops: seq<seq<int>>, result: int)
  requires max_count_pre(m, n, ops)

method max_count(m: int, n: int, ops: seq<seq<int>>) returns (result: int)
  requires max_count_pre(m, n, ops)
  ensures max_count_post(m, n, ops, result)
```
