# Beautiful Array

An array `nums` of length `n` is **beautiful** if:

- `nums` is a permutation of the integers in the range $[1, n]$.
- For every $0 <= i < j < n$, there is no index `k` with $i < k < j$ where $2 * nums[k] == nums[i] + nums[j]$.

Given the integer `n`, return any **beautiful** array `nums` of length `n`. There will be at least one valid answer for the given `n`.

## Example 1:

> **Input:** n = 4
> **Output:** [2,1,4,3]

## Example 2:

> **Input:** n = 5
> **Output:** [3,1,2,5,4]

## Constraints:

- $1 <= n <= 1000$

## Starter Code

```dafny
predicate beautiful_array_pre(n: int)

predicate beautiful_array_post(n: int, result: seq<int>)
  requires beautiful_array_pre(n)

method beautiful_array(n: int) returns (result: seq<int>)
  requires beautiful_array_pre(n)
  ensures beautiful_array_post(n, result)
```
