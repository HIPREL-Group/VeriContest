# Count of Range Sum

Given an integer array `nums` and two integers `lower` and `upper`, return the number of range sums that lie in `[lower, upper]` (inclusive).

Range sum `S(i, j)` is defined as the sum of `nums[i..=j]` where `i <= j`.

## Example 1

> Input: nums = [-2, 5, -1], lower = -2, upper = 2
> Output: 3
> Explanation: The three valid ranges are [0,0], [2,2], and [0,2], with sums -2, -1, and 2.

## Example 2

> Input: nums = [0], lower = 0, upper = 0
> Output: 1

## Constraints

- `1 <= nums.length <= 10^5`
- `-2^31 <= nums[i] <= 2^31 - 1`
- `-10^5 <= lower <= upper <= 10^5`
- The answer is guaranteed to fit in a 32-bit integer.

## Starter Code

```dafny
predicate count_range_sum_pre(nums: seq<int>, lower: int, upper: int)

predicate count_range_sum_post(nums: seq<int>, lower: int, upper: int, res: int)
  requires count_range_sum_pre(nums, lower, upper)

method count_range_sum(nums: seq<int>, lower: int, upper: int) returns (res: int)
  requires count_range_sum_pre(nums, lower, upper)
  ensures count_range_sum_post(nums, lower, upper, res)
```
