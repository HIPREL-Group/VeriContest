# Subarray Product Less Than K

Given an array of integers `nums` and an integer `k`, return *the number of contiguous subarrays where the product of all the elements in the subarray is strictly less than *`k`.

 

Example 1:

```
**Input:** nums = [10,5,2,6], k = 100
**Output:** 8
**Explanation:** The 8 subarrays that have product less than 100 are:
[10], [5], [2], [6], [10, 5], [5, 2], [2, 6], [5, 2, 6]
Note that [10, 5, 2] is not included as the product of 100 is not strictly less than k.
```

Example 2:

```
**Input:** nums = [1,2,3], k = 0
**Output:** 0
```

 

**Constraints:**

	- `1 <= nums.length <= 3 * 10^4`

	- `1 <= nums[i] <= 1000`

	- `0 <= k <= 10^6`

## Starter Code

```dafny
predicate num_subarray_product_less_than_k_pre(nums: seq<int>, k: int)

predicate num_subarray_product_less_than_k_post(nums: seq<int>, k: int, res: int)
  requires num_subarray_product_less_than_k_pre(nums, k)

method num_subarray_product_less_than_k(nums: seq<int>, k: int) returns (res: int)
  requires num_subarray_product_less_than_k_pre(nums, k)
  ensures num_subarray_product_less_than_k_post(nums, k, res)
```
