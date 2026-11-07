# Sum of Two Integers

Given two integers `a` and `b`, return the sum of the two integers without using the operators `+` and `-`.

## Example 1:

> **Input:** a = 1, b = 2
> **Output:** 3

## Example 2:

> **Input:** a = 2, b = 3
> **Output:** 5

## Constraints:

- `-1000 <= a, b <= 1000`

## Starter Code

```dafny
predicate get_sum_pre(a: int, b: int)

predicate get_sum_post(a: int, b: int, res: int)
  requires get_sum_pre(a, b)

method get_sum(a: int, b: int) returns (res: int)
  requires get_sum_pre(a, b)
  ensures get_sum_post(a, b, res)
```
