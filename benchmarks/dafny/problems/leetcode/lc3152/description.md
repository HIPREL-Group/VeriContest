# Special Array II

An array is considered **special** if every pair of its adjacent elements contains two numbers with different parity.

You are given an integer array `nums` and a 2D integer array `queries`. For each `queries[i] = [from_i, to_i]`, determine whether the subarray `nums[from_i..to_i]` is special.

Return a boolean array `answer` such that `answer[i]` is `true` if `nums[from_i..to_i]` is special.

## Example 1:

> **Input:** nums = [3,4,1,2,6], queries = [[0,4]]
> **Output:** [false]
> **Explanation:** The subarray is `[3,4,1,2,6]`. `2` and `6` are both even.

## Example 2:

> **Input:** nums = [4,3,1,6], queries = [[0,2],[2,3]]
> **Output:** [false,true]
> **Explanation:**
> 1. The subarray is `[4,3,1]`. `3` and `1` are both odd, so the answer is `false`.
> 2. The subarray is `[1,6]`. Its only adjacent pair has different parity, so the answer is `true`.

## Constraints:

- `1 <= nums.length <= 10^5`
- `1 <= nums[i] <= 10^5`
- `1 <= queries.length <= 10^5`
- `queries[i].length == 2`
- `0 <= queries[i][0] <= queries[i][1] <= nums.length - 1`

## Starter Code

```dafny
predicate is_array_special_pre(nums: seq<int>, queries: seq<seq<int>>)

predicate is_array_special_post(nums: seq<int>, queries: seq<seq<int>>, answer: seq<bool>)
  requires is_array_special_pre(nums, queries)

method is_array_special(nums: seq<int>, queries: seq<seq<int>>) returns (answer: seq<bool>)
  requires is_array_special_pre(nums, queries)
  ensures is_array_special_post(nums, queries, answer)
```
