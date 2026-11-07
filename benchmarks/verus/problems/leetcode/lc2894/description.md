# Divisible and Non-divisible Sums Difference

You are given positive integers `n` and `m`.

Define two integers as follows:

- `num1`: The sum of all integers in the range `[1, n]` (both **inclusive**) that are **not divisible** by `m`.
- `num2`: The sum of all integers in the range `[1, n]` (both **inclusive**) that are **divisible** by `m`.

Return *the integer* `num1 - num2`.

## Example 1:

> **Input:** `n = 10`, `m = 3`
> **Output:** `19`
> **Explanation:** 
> - Integers not divisible by 3: `[1,2,4,5,7,8,10]`, sum is 37.
> - Integers divisible by 3: `[3,6,9]`, sum is 18.
> We return `37 - 18 = 19`.

## Constraints:

- `1 <= n, m <= 1000`

## Starter Code

```rust
impl Solution {
    pub fn difference_of_sums(n: i32, m: i32) -> i32 {
        
    }
}
```
