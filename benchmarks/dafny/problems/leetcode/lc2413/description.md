# Smallest Even Multiple

Given a positive integer `n`, return the smallest positive integer that is a multiple of both `2` and `n`.

## Example 1:

> **Input:** n = 5
> **Output:** 10
> **Explanation:** The smallest multiple of both 5 and 2 is 10.

## Example 2:

> **Input:** n = 6
> **Output:** 6
> **Explanation:** The smallest multiple of both 6 and 2 is 6.

## Constraints:

- $1 <= n <= 150$

## Starter Code

```dafny
predicate smallest_even_multiple_pre(n: int)

predicate smallest_even_multiple_post(n: int, result: int)
  requires smallest_even_multiple_pre(n)

method smallest_even_multiple(n: int) returns (result: int)
  requires smallest_even_multiple_pre(n)
  ensures smallest_even_multiple_post(n, result)
```
