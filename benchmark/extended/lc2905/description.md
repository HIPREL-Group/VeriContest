# Find Indices With Index and Value Difference II

You are given a 0-indexed integer array `nums` of length `n`, along with two integers `indexDifference` and `valueDifference`.

Find two indices `i` and `j` in the range $[0, n - 1]$ such that:

- $|i - j| \geq \texttt{indexDifference}$
- $|\texttt{nums}[i] - \texttt{nums}[j]| \geq \texttt{valueDifference}$

Return `[i, j]` if such indices exist. Otherwise, return `[-1, -1]`. If there are multiple valid answers, return any of them.

**Note:** `i` and `j` may be equal.

## Example 1:

> **Input:** nums = [5, 1, 4, 1], indexDifference = 2, valueDifference = 4
> **Output:** [0, 3]
> **Explanation:** Choosing `i = 0` and `j = 3` works because $|0 - 3| = 3 \geq 2$ and $|5 - 1| = 4 \geq 4$.

## Example 2:

> **Input:** nums = [2, 1], indexDifference = 0, valueDifference = 0
> **Output:** [0, 0]
> **Explanation:** Choosing `i = 0` and `j = 0` works because $|0 - 0| = 0 \geq 0$ and $|2 - 2| = 0 \geq 0$.

## Example 3:

> **Input:** nums = [1, 2, 3], indexDifference = 2, valueDifference = 4
> **Output:** [-1, -1]
> **Explanation:** No pair of indices satisfies both conditions.

## Constraints:

- $1 \leq n == \texttt{nums.length} \leq 10^5$
- $0 \leq \texttt{nums}[i] \leq 10^9$
- $0 \leq \texttt{indexDifference} \leq 10^5$
- $0 \leq \texttt{valueDifference} \leq 10^9$

## Starter Code

```rust
impl Solution {
    pub fn find_indices(nums: Vec<i32>, index_difference: i32, value_difference: i32) -> Vec<i32> {
        
    }
}
```
