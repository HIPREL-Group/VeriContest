# Range Sum Query - Immutable

Given an integer array `nums`, handle multiple queries of the following type:

- Calculate the **sum** of the elements of `nums` between indices `left` and `right` **inclusive** where `left <= right`.

Implement the `NumArray` class:

- `NumArray(nums)` Initializes the object with the integer array `nums`.
- `sum_range(left, right)` Returns the **sum** of the elements of `nums` between indices `left` and `right` **inclusive** (i.e. `nums[left] + nums[left + 1] + ... + nums[right]`).

## Example 1:

> **Input:** ["NumArray", "sumRange", "sumRange", "sumRange"] with [[[-2, 0, 3, -5, 2, -1]], [0, 2], [2, 5], [0, 5]]
> **Output:** [null, 1, -1, -3]
>
> **Explanation:** NumArray is built with [-2, 0, 3, -5, 2, -1]. sumRange(0, 2) = (-2)+0+3 = 1; sumRange(2, 5) = 3+(-5)+2+(-1) = -1; sumRange(0, 5) = -3.

## Constraints:

- `1 <= nums.length <= 10^4`
- `-10^5 <= nums[i] <= 10^5`
- `0 <= left <= right < nums.length`
- At most `10^4` calls will be made to `sumRange`.

## Starter Code

```dafny
predicate sum_range_pre(nums: seq<int>, left: int, right: int)

predicate sum_range_post(nums: seq<int>, left: int, right: int, result: int)
  requires sum_range_pre(nums, left, right)

method sum_range(nums: seq<int>, left: int, right: int) returns (result: int)
  requires sum_range_pre(nums, left, right)
  ensures sum_range_post(nums, left, right, result)
```
