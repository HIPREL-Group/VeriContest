# Diagonal Traverse II

Given a 2D integer array `nums`, return all elements of `nums` in diagonal order as shown in the below images.

## Example 1:

> **Input:** nums = [[1,2,3],[4,5,6],[7,8,9]]
> **Output:** [1,4,2,7,5,3,8,6,9]

## Example 2:

> **Input:** nums = [[1,2,3,4,5],[6,7],[8],[9,10,11],[12,13,14,15,16]]
> **Output:** [1,6,2,8,7,3,9,4,12,10,5,13,11,14,15,16]

## Constraints:

- $1 \leq$ `nums.length` $\leq 10^5$
- $1 \leq$ `nums[i].length` $\leq 10^5$
- $1 \leq$ `sum(nums[i].length)` $\leq 10^5$
- $1 \leq$ `nums[i][j]` $\leq 10^5$

## Starter Code

```dafny
predicate find_diagonal_order_pre(nums: seq<seq<int>>)

predicate find_diagonal_order_post(nums: seq<seq<int>>, result: seq<int>)
  requires find_diagonal_order_pre(nums)

method find_diagonal_order(nums: seq<seq<int>>) returns (result: seq<int>)
  requires find_diagonal_order_pre(nums)
  ensures find_diagonal_order_post(nums, result)
```
