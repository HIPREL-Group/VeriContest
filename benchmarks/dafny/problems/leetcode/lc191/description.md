# 191. Number of 1 Bits

Given a positive integer `n`, write a function that returns the number of set bits in its binary representation (also known as the Hamming weight).

A set bit refers to a bit in the binary representation of a number that has a value of `1`.

## Example 1:
> **Input:** n = 11
> **Output:** 3
> **Explanation:**
> The input binary string 1011 has a total of three set bits.

## Example 2:
> **Input:** n = 128
> **Output:** 1
> **Explanation:**
> The input binary string 10000000 has a total of one set bit.

## Example 3:
> **Input:** n = 2147483645
> **Output:** 30
> **Explanation:**
> The input binary string 1111111111111111111111111111101 has a total of thirty set bits.

## Constraints:

- $1 <= n <= 2^{31} - 1$

## Starter Code

```dafny
predicate hamming_weight_pre(n: int)

predicate hamming_weight_post(n: int, res: int)
  requires hamming_weight_pre(n)

method hamming_weight(n: int) returns (res: int)
  requires hamming_weight_pre(n)
  ensures hamming_weight_post(n, res)
```
