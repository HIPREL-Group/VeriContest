# Minimum Equal Sum of Two Arrays After Replacing Zeros

You are given two arrays `nums1` and `nums2` consisting of positive integers.

You have to replace **all** the `0`'s in both arrays with **strictly** positive integers such that the sum of elements of both arrays becomes **equal**.

Return *the **minimum** equal sum you can obtain, or *`-1`* if it is impossible*.

 

Example 1:

```
**Input:** nums1 = [3,2,0,1,0], nums2 = [6,5,0]
**Output:** 12
**Explanation:** We can replace 0's in the following way:
- Replace the two 0's in nums1 with the values 2 and 4. The resulting array is nums1 = [3,2,2,1,4].
- Replace the 0 in nums2 with the value 1. The resulting array is nums2 = [6,5,1].
Both arrays have an equal sum of 12. It can be shown that it is the minimum sum we can obtain.
```

Example 2:

```
**Input:** nums1 = [2,0,2,0], nums2 = [1,4]
**Output:** -1
**Explanation:** It is impossible to make the sum of both arrays equal.
```

 

**Constraints:**

	- `1 <= nums1.length, nums2.length <= 10^5`

	- `0 <= nums1[i], nums2[i] <= 10^6`

## Starter Code

```rust
impl Solution {
    pub fn min_sum(nums1: Vec<i32>, nums2: Vec<i32>) -> i64 {
        
    }
}
```
