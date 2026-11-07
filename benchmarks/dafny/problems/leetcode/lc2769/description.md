# Find the Maximum Achievable Number

Given two integers, `num` and `t`. A number `x` is achievable if it can become equal to `num` after applying the following operation at most `t` times:

- Increase or decrease `x` by `1`, and simultaneously increase or decrease `num` by `1`.

Return the maximum possible value of `x`.

## Example 1:

> **Input:** num = 4, t = 1
> **Output:** 6

## Example 2:

> **Input:** num = 3, t = 2
> **Output:** 7

## Constraints:

- `1 <= num, t <= 50`

## Starter Code

```dafny
predicate the_maximum_achievable_x_pre(num: int, t: int)

predicate the_maximum_achievable_x_post(num: int, t: int, result: int)
  requires the_maximum_achievable_x_pre(num, t)

method the_maximum_achievable_x(num: int, t: int) returns (result: int)
  requires the_maximum_achievable_x_pre(num, t)
  ensures the_maximum_achievable_x_post(num, t, result)
```
