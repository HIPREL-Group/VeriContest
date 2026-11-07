# Earliest Second to Mark Indices I

You are given two **1-indexed** integer arrays, `nums` and `changeIndices`, having lengths `n` and `m`, respectively.

Initially, all indices in `nums` are unmarked. Your task is to mark **all** indices in `nums`.

In each second `s`, in order from `1` to `m` (**inclusive**), you can perform **one** of the following operations:

- Choose an index `i` in the range `[1, n]` and decrement `nums[i]` by `1`.
- If `nums[changeIndices[s]]` is equal to `0`, mark the index `changeIndices[s]`.
- Do nothing.

Return an integer denoting the **earliest second** in the range `[1, m]` when **all** indices in `nums` can be marked by choosing operations optimally, or `-1` if it is impossible.

## Example 1:

> **Input:** nums = [2,2,0], changeIndices = [2,2,2,2,3,2,2,1]
> **Output:** 8
> **Explanation:**
> - Second 1: Decrement index 1. `nums = [1,2,0]`
> - Second 2: Decrement index 1. `nums = [0,2,0]`
> - Second 3: Decrement index 2. `nums = [0,1,0]`
> - Second 4: Decrement index 2. `nums = [0,0,0]`
> - Second 5: Mark index 3.
> - Second 6: Mark index 2.
> - Second 7: Do nothing.
> - Second 8: Mark index 1.
> All indices are marked, and it is impossible earlier.

## Example 2:

> **Input:** nums = [1,3], changeIndices = [1,1,1,2,1,1,1]
> **Output:** 6
> **Explanation:**
> - Second 1: Decrement index 2. `nums = [1,2]`
> - Second 2: Decrement index 2. `nums = [1,1]`
> - Second 3: Decrement index 2. `nums = [1,0]`
> - Second 4: Mark index 2.
> - Second 5: Decrement index 1. `nums = [0,0]`
> - Second 6: Mark index 1.
> All indices are marked, and it is impossible earlier.

## Example 3:

> **Input:** nums = [0,1], changeIndices = [2,2,2]
> **Output:** -1
> **Explanation:** Index 1 never appears in `changeIndices`, so marking all indices is impossible.

## Constraints:

- `1 <= n == nums.length <= 2000`
- `0 <= nums[i] <= 10^9`
- `1 <= m == changeIndices.length <= 2000`
- `1 <= changeIndices[i] <= n`

## Starter Code

```rust
impl Solution {
    pub fn earliest_second_to_mark_indices(nums: Vec<i32>, change_indices: Vec<i32>) -> i32 {
        
    }
}
```
