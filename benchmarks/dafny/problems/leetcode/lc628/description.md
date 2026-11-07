# Maximum Product of Three Numbers

Given an integer array `nums`, find three numbers whose product is maximum and return the maximum product.

## Example 1:

> **Input:** nums = [1,2,3]
> **Output:** 6

## Example 2:

> **Input:** nums = [1,2,3,4]
> **Output:** 24

## Example 3:

> **Input:** nums = [-1,-2,-3]
> **Output:** -6

## Constraints:

- $3 \leq \text{nums.length} \leq 10^4$
- $-1000 \leq \text{nums}[i] \leq 1000$

## Starter Code

```dafny
predicate maximum_product_pre(nums: seq<int>)

predicate maximum_product_post(nums: seq<int>, result: int)
  requires maximum_product_pre(nums)

method maximum_product(nums: seq<int>) returns (result: int)
  requires maximum_product_pre(nums)
  ensures maximum_product_post(nums, result)
```
