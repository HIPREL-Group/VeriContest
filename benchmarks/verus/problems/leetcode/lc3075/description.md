# Maximize Happiness of Selected Children

You are given an array `happiness` of length `n`, and a positive integer `k`.

There are `n` children standing in a queue, where the `i^th` child has happiness value `happiness[i]`. You want to select `k` children from these `n` children in `k` turns.

In each turn, when you select a child, the happiness value of all the children that have not been selected till now decreases by `1`. The happiness value cannot become negative and gets decremented only if it is positive.

Return the maximum sum of the happiness values of the selected children you can achieve by selecting `k` children.

## Example 1:

> **Input:** happiness = [1,2,3], k = 2  
> **Output:** 4  
> **Explanation:** We can pick 2 children in the following way:  
> Pick the child with happiness value `3`. The happiness of the remaining children becomes `[0,1]`.  
> Pick the child with happiness value `1`. The happiness of the remaining child becomes `[0]`.  
> The sum is `3 + 1 = 4`.

## Example 2:

> **Input:** happiness = [1,1,1,1], k = 2  
> **Output:** 1  
> **Explanation:** We can pick 2 children in the following way:  
> Pick any child with happiness value `1`. The happiness of the remaining children becomes `[0,0,0]`.  
> Pick the child with happiness value `0`. The happiness of the remaining children stays `[0,0]`.  
> The sum is `1 + 0 = 1`.

## Example 3:

> **Input:** happiness = [2,3,4,5], k = 1  
> **Output:** 5  
> **Explanation:** Pick the child with happiness value `5`. The sum is `5`.

## Constraints:

- `1 <= n == happiness.length <= 2 * 10^5`
- `1 <= happiness[i] <= 10^8`
- `1 <= k <= n`

## Starter Code

```rust
impl Solution {
    pub fn maximum_happiness_sum(happiness: Vec<i32>, k: i32) -> i64 {
        
    }
}
```
