# Climbing Stairs

You are climbing a staircase. It takes `n` steps to reach the top.

Each time you can either climb `1` or `2` steps. In how many distinct ways can you climb to the top?

## Example 1:

> Input: n = 2
> Output: 2
> Explanation: There are two ways to climb to the top.
> 1. 1 step + 1 step
> 2. 2 steps

## Example 2:

> Input: n = 3
> Output: 3
> Explanation: There are three ways to climb to the top.
> 1. 1 step + 1 step + 1 step
> 2. 1 step + 2 steps
> 3. 2 steps + 1 step

## Constraints:

- $1 <= n <= 45$

## Starter Code

```dafny
predicate climb_stairs_pre(n: int)

predicate climb_stairs_post(n: int, res: int)
  requires climb_stairs_pre(n)

method climb_stairs(n: int) returns (res: int)
  requires climb_stairs_pre(n)
  ensures climb_stairs_post(n, res)
```
