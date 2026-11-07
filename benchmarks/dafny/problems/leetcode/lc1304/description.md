# Find N Unique Integers Sum up to Zero

Given an integer `n`, return any array containing `n` unique integers such that they add up to `0`.

## Example 1:

> **Input:** n = 5
> **Output:** [-7,-1,1,3,4]
> **Explanation:** These arrays are also accepted: [-5,-1,1,2,3], [-3,-1,2,-2,4].

## Example 2:

> **Input:** n = 3
> **Output:** [-1,0,1]

## Example 3:

> **Input:** n = 1
> **Output:** [0]

## Constraints:

- `1 <= n <= 1000`

## Starter Code

```dafny
predicate sum_zero_pre(n: int)

predicate sum_zero_post(n: int, result: seq<int>)
  requires sum_zero_pre(n)

method sum_zero(n: int) returns (result: seq<int>)
  requires sum_zero_pre(n)
  ensures sum_zero_post(n, result)
```
