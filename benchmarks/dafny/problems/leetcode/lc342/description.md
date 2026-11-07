# 342. Power of Four
Given an integer n, return `true` if it is a power of four. Otherwise, return `false`.

An integer `n` is a power of four, if there exists an integer `x` such that `n == 4**x`.

## Example 1:
> **Input:** n = 16  
> **Output:** true


## Example 2:
> **Input:** n = 5  
> **Output:** false

## Example 3:
> **Input:** n = 1  
> **Output:** true

## Constraints:

- $-2^{31} <= n <= 2^{31} - 1$

## Starter Code

```dafny
predicate is_power_of_four_pre(n: int)

predicate is_power_of_four_post(n: int, res: bool)
  requires is_power_of_four_pre(n)

method is_power_of_four(n: int) returns (res: bool)
  requires is_power_of_four_pre(n)
  ensures is_power_of_four_post(n, res)
```
