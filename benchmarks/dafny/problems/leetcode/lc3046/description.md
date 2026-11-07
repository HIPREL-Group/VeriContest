# Split the Array

You are given an integer array `nums` of even length. You have to split the array into two parts `nums1` and `nums2` such that:

- `nums1.length == nums2.length == nums.length / 2`
- `nums1` contains distinct elements
- `nums2` contains distinct elements

Return `true` if it is possible to split the array, and `false` otherwise.

## Example 1:

> **Input:** nums = [1,1,2,2,3,4]
> **Output:** true
> **Explanation:** One possible split is nums1 = [1,2,3] and nums2 = [1,2,4].

## Example 2:

> **Input:** nums = [1,1,1,1]
> **Output:** false
> **Explanation:** The only possible split is nums1 = [1,1] and nums2 = [1,1]. Neither part contains distinct elements.

## Constraints:

- $1 <= nums.length <= 100$
- $nums.length \% 2 == 0$
- $1 <= nums[i] <= 100$

## Starter Code

```dafny
predicate is_possible_to_split_pre(nums: seq<int>)

predicate is_possible_to_split_post(nums: seq<int>, res: bool)
  requires is_possible_to_split_pre(nums)

method is_possible_to_split(nums: seq<int>) returns (res: bool)
  requires is_possible_to_split_pre(nums)
  ensures is_possible_to_split_post(nums, res)
```
