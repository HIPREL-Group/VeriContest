# Maximum Product of Two Digits

You are given a positive integer `n`.

Return the maximum product of any two digits in `n`.

You may use the same digit value twice only if that digit appears at least twice in `n`.

## Example 1:

> **Input:** n = 31
> **Output:** 3

## Example 2:

> **Input:** n = 22
> **Output:** 4

## Example 3:

> **Input:** n = 124
> **Output:** 8

## Constraints:

- `10 <= n <= 10^9`

## Starter Code

```dafny
predicate max_product_pre(n: int)

predicate max_product_post(n: int, res: int)
  requires max_product_pre(n)

method max_product(n: int) returns (res: int)
  requires max_product_pre(n)
  ensures max_product_post(n, res)
```
