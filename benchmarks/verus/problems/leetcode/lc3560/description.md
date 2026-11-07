# Find Minimum Log Transportation Cost

You are given integers `n`, `m`, and `k`.

There are two logs of lengths `n` and `m` units, and three trucks where each truck can carry one log of length at most `k`.

You may cut a log into smaller pieces. Cutting a log of length `x` into two logs of lengths `len1` and `len2` costs `len1 * len2`, where `len1 + len2 = x`.

Return the minimum total cutting cost needed so all resulting logs can be transported using the three trucks. If no cut is needed, return `0`.

## Example 1:

> **Input:** n = 6, m = 5, k = 5
> **Output:** 5
> **Explanation:** Cut the log of length 6 into lengths 1 and 5, costing `1 * 5 = 5`. Then the three logs 1, 5, and 5 each fit in one truck.

## Example 2:

> **Input:** n = 4, m = 4, k = 6
> **Output:** 0
> **Explanation:** Both logs already fit in the trucks.

## Constraints:

- `2 <= k <= 10^5`
- `1 <= n, m <= 2 * k`
- The input is generated such that it is always possible to transport the logs.

## Starter Code

```rust
impl Solution {
    pub fn min_cutting_cost(n: i32, m: i32, k: i32) -> i64 {
        
    }
}
```
