# Remove Zeros in Decimal Representation

You are given a **positive** integer `n`.

Return the integer obtained by removing all zeros from the decimal representation of `n`.

## Example 1:

> **Input:** n = 1020030
> **Output:** 123
>
> **Explanation:**
> After removing all zeros from 1**0**2**00**3**0**, we get 123.

## Example 2:

> **Input:** n = 1
> **Output:** 1
>
> **Explanation:**
> 1 has no zero in its decimal representation. Therefore, the answer is 1.

## Constraints:

- `1 <= n <= 10^15`

## Starter Code

```dafny
predicate remove_zeros_pre(n: int)

predicate remove_zeros_post(n: int, res: int)
  requires remove_zeros_pre(n)

method remove_zeros(n: int) returns (res: int)
  requires remove_zeros_pre(n)
  ensures remove_zeros_post(n, res)
```
