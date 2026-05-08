# Minimum Flips to Make a OR b Equal to c

Given 3 positive numbers `a`, `b` and `c`, return the minimum flips required in some bits of `a` and `b` to make `a OR b == c` (bitwise OR operation).

A flip operation consists of changing **any** single bit 1 to 0 or changing the bit 0 to 1 in their binary representation.

## Example 1:

> **Input:** a = 2, b = 6, c = 5
> **Output:** 3
> **Explanation:** After flips a = 1, b = 4, c = 5 such that (a OR b == c)

## Example 2:

> **Input:** a = 4, b = 2, c = 7
> **Output:** 1

## Example 3:

> **Input:** a = 1, b = 2, c = 3
> **Output:** 0

## Constraints:

- $1 \leq a \leq 10^9$
- $1 \leq b \leq 10^9$
- $1 \leq c \leq 10^9$

## Starter Code

```rust
impl Solution {
    pub fn min_flips(a: i32, b: i32, c: i32) -> i32 {
        
    }
}
```
