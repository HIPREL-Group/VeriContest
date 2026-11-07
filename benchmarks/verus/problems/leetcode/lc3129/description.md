# Find All Possible Stable Binary Arrays I

You are given 3 positive integers `zero`, `one`, and `limit`.

A binary array `arr` is called **stable** if:

- The number of occurrences of `0` in `arr` is exactly `zero`.
- The number of occurrences of `1` in `arr` is exactly `one`.
- Each subarray of `arr` with size greater than `limit` must contain both `0` and `1`.

Return the total number of stable binary arrays.

Since the answer may be very large, return it modulo `10^9 + 7`.

## Example 1:

> **Input:** zero = 1, one = 1, limit = 2
> **Output:** 2

## Example 2:

> **Input:** zero = 1, one = 2, limit = 1
> **Output:** 1

## Example 3:

> **Input:** zero = 3, one = 3, limit = 2
> **Output:** 14

## Constraints:

- `1 <= zero, one, limit <= 200`

## Starter Code

```rust
impl Solution {
    pub fn number_of_stable_arrays(zero: i32, one: i32, limit: i32) -> i32 {
        
    }
}
```
