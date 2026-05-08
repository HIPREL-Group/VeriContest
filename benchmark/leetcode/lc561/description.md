# Array Partition

Given an integer array `nums` of `2n` integers, group these integers into `n` pairs `(a1, b1), (a2, b2), ..., (an, bn)` such that the sum of `min(ai, bi)` for all `i` is maximized. Return the maximized sum.

## Example 1:

> **Input:** nums = [1,4,3,2]
> **Output:** 4
> **Explanation:** The optimal pairing is (1,2) and (3,4). min(1,2) + min(3,4) = 1 + 3 = 4.

## Example 2:

> **Input:** nums = [6,2,6,5,1,2]
> **Output:** 9
> **Explanation:** Pairs are (2,1), (2,5), (6,6). min(2,1)+min(2,5)+min(6,6) = 1+2+6 = 9.

## Constraints:

- `1 <= n <= 10^4`
- `nums.length == 2 * n`
- `-10^4 <= nums[i] <= 10^4`

## Starter Code

```rust
impl Solution {
    pub fn array_pair_sum(nums: Vec<i32>) -> i32 {
        
    }
}
```
