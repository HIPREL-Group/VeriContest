# Check Divisibility by Digit Sum and Product

You are given a positive integer `n`. Determine whether `n` is divisible by the sum of the following two values:

- The **digit sum** of `n` (the sum of its digits).
- The **digit product** of `n` (the product of its digits).

Return `true` if `n` is divisible by this sum; otherwise, return `false`.

## Example 1:

> **Input:** n = 99
> **Output:** true
> **Explanation:** The digit sum of `99` is `9 + 9 = 18`, and the digit product is `9 * 9 = 81`. Their sum is `99`, and `99` is divisible by `99`.

## Example 2:

> **Input:** n = 23
> **Output:** false
> **Explanation:** The digit sum of `23` is `2 + 3 = 5`, and the digit product is `2 * 3 = 6`. Their sum is `11`, and `23` is not divisible by `11`.

## Constraints:

- $1 <= n <= 10^6$

## Starter Code

```rust
impl Solution {
    pub fn check_divisibility(n: i32) -> bool {
        
    }
}
```
