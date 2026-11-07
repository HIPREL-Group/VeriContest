# Maximum Average Subarray I

You are given an integer array `nums` consisting of `n` elements, and an integer `k`.

Find a contiguous subarray whose **length is equal to** `k` that has the maximum average value and return *this value*. Any answer with a calculation error less than `10^-5` will be accepted.

## Example 1:

> **Input:** nums = [1,12,-5,-6,50,3], k = 4
> **Output:** 12.75000
> **Explanation:** Maximum average is (12 - 5 - 6 + 50) / 4 = 51 / 4 = 12.75

## Example 2:

> **Input:** nums = [5], k = 1
> **Output:** 5.00000

**Constraints:**

- `n == nums.length`
- `1 <= k <= n <= 10^5`
- `-10^4 <= nums[i] <= 10^4`

## Starter Code

In the Dafny version, `find_max_average_core` returns the maximum sum of a contiguous subarray of length `k`. The testcases give `find_max_average(nums, k)`, which is that sum divided by `k`.

```dafny
predicate find_max_average_core_pre(nums: seq<int>, k: int)

predicate find_max_average_core_post(nums: seq<int>, k: int, result: int)
  requires find_max_average_core_pre(nums, k)

method find_max_average_core(nums: seq<int>, k: int) returns (result: int)
  requires find_max_average_core_pre(nums, k)
  ensures find_max_average_core_post(nums, k, result)
```
