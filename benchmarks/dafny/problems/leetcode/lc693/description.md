# 693. Binary Number with Alternating Bits

Given a positive integer `n`, check whether it has alternating bits: namely, if two adjacent bits will always have different values.

## Example 1:

> **Input:** n = 5
> **Output:** true
> **Explanation:** The binary representation of 5 is: 101

## Example 2:

> **Input:** n = 7
> **Output:** false
> **Explanation:** The binary representation of 7 is: 111.

## Example 3:

> **Input:** n = 11
> **Output:** false
> **Explanation:** The binary representation of 11 is: 1011.

## Constraints:

- $1 \leq n \leq 2^{31} - 1$

## Starter Code

```dafny
predicate has_alternating_bits_pre(n: int)

predicate has_alternating_bits_post(n: int, result: bool)
  requires has_alternating_bits_pre(n)

method has_alternating_bits(n: int) returns (result: bool)
  requires has_alternating_bits_pre(n)
  ensures has_alternating_bits_post(n, result)
```
