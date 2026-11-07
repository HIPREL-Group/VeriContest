# Mark Elements on Array by Performing Queries

You are given a **0-indexed** array `nums` of size `n` consisting of positive integers.

You are also given a 2D array `queries` of size `m` where `queries[i] = [index_i, k_i]`.

Initially all elements of the array are **unmarked**.

You need to apply `m` queries on the array in order, where on the `i^th` query you do the following:

- Mark the element at index `index_i` if it is not already marked.
- Then mark `k_i` unmarked elements in the array with the **smallest** values. If multiple such elements exist, mark the ones with the smallest indices. If fewer than `k_i` unmarked elements exist, mark all of them.

Return an array `answer` of size `m` where `answer[i]` is the **sum** of unmarked elements in the array after the `i^th` query.

## Example 1:

> **Input:** nums = [1,2,2,1,2,3,1], queries = [[1,2],[3,3],[4,2]]
> **Output:** [8,3,0]

## Example 2:

> **Input:** nums = [1,4,2,3], queries = [[0,1]]
> **Output:** [7]

## Constraints:

- `n == nums.length`
- `m == queries.length`
- `1 <= m <= n <= 10^5`
- `1 <= nums[i] <= 10^5`
- `queries[i].length == 2`
- `0 <= index_i, k_i <= n - 1`

## Starter Code

```rust
impl Solution {
    pub fn unmarked_sum_array(nums: Vec<i32>, queries: Vec<Vec<i32>>) -> Vec<i64> {
        
    }
}
```
