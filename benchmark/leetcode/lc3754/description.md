# Concatenate Non-Zero Digits and Multiply by Sum I

You are given an integer `n`.

Form a new integer `x` by concatenating all the **non-zero digits** of `n` in their original order. If there are no non-zero digits, set `x = 0`.

Let `sum` be the sum of digits in `x`.

Return `x * sum`.

## Example 1:

> **Input:** n = 10203004
> **Output:** 12340
> **Explanation:**
> The non-zero digits are 1, 2, 3, and 4, so `x = 1234`.
> The sum of digits is `1 + 2 + 3 + 4 = 10`.
> Therefore, the answer is `1234 * 10 = 12340`.

## Example 2:

> **Input:** n = 1000
> **Output:** 1
> **Explanation:**
> The non-zero digit is 1, so `x = 1` and `sum = 1`.
> Therefore, the answer is `1 * 1 = 1`.

## Constraints:

- `0 <= n <= 10^9`

## Starter Code

```rust
impl Solution {
    pub fn sum_and_multiply(n: i32) -> i64 {
        
    }
}
```
