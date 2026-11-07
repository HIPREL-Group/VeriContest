# Number of Subarrays with Bounded Maximum

Given an integer array `nums` and two integers `left` and `right`, return *the number of contiguous non-empty **subarrays** such that the value of the maximum array element in that subarray is in the range *`[left, right]`.

The test cases are generated so that the answer will fit in a **32-bit** integer.

 

Example 1:

```
**Input:** nums = [2,1,4,3], left = 2, right = 3
**Output:** 3
**Explanation:** There are three subarrays that meet the requirements: [2], [2, 1], [3].
```

Example 2:

```
**Input:** nums = [2,9,2,5,6], left = 2, right = 8
**Output:** 7
```

 

**Constraints:**

	- `1 <= nums.length <= 10^5`

	- `0 <= nums[i] <= 10^9`

	- `0 <= left <= right <= 10^9`

## Starter Code

```dafny
predicate num_subarray_bounded_max_pre(nums: seq<int>, left: int, right: int)

predicate num_subarray_bounded_max_post(nums: seq<int>, left: int, right: int, res: int)
  requires num_subarray_bounded_max_pre(nums, left, right)

method num_subarray_bounded_max(nums: seq<int>, left: int, right: int) returns (res: int)
  requires num_subarray_bounded_max_pre(nums, left, right)
  ensures num_subarray_bounded_max_post(nums, left, right, res)
```
