# Mirror Distance of an Integer

You are given an integer `n`.

Define its **mirror distance** as `abs(n - reverse(n))`, where `reverse(n)` is the integer formed by reversing the digits of `n`.

Return an integer denoting the mirror distance of `n`.

`abs(x)` denotes the absolute value of `x`.

## Example 1:

> **Input:** n = 25  
> **Output:** 27

## Example 2:

> **Input:** n = 10  
> **Output:** 9

## Example 3:

> **Input:** n = 7  
> **Output:** 0

## Constraints:

- `1 <= n <= 10^9`

## Starter Code

```dafny
predicate mirror_distance_pre(n: int)

predicate mirror_distance_post(n: int, res: int)
  requires mirror_distance_pre(n)

method mirror_distance(n: int) returns (res: int)
  requires mirror_distance_pre(n)
  ensures mirror_distance_post(n, res)
```
