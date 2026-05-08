# Minimum Swaps To Make Sequences Increasing

You are given two integer arrays `nums1` and `nums2` of the same length `n`. In one operation you may swap `nums1[i]` and `nums2[i]` for any index `0 <= i < n`. Return the **minimum number of swaps** to make both arrays strictly increasing. The test cases are generated so that a solution always exists.

## Example 1:

> **Input:** nums1 = [1,3,5,4], nums2 = [1,2,3,7]
> **Output:** 1
> **Explanation:** Swap nums1[3] and nums2[3]. Then nums1 = [1,3,5,7] and nums2 = [1,2,3,4], both strictly increasing.

## Example 2:

> **Input:** nums1 = [0,3,5,8,9], nums2 = [2,1,4,6,7]
> **Output:** 1

## Constraints:

- $2 \leq \texttt{nums1.length} \leq 10^5$
- $\texttt{nums1.length} = \texttt{nums2.length}$
- $0 \leq \texttt{nums1[i]},\, \texttt{nums2[i]} \leq 2 \times 10^5$

## Starter Code

```rust
impl Solution {
    pub fn min_swap(nums1: Vec<i32>, nums2: Vec<i32>) -> i32 {
        
    }
}
```
