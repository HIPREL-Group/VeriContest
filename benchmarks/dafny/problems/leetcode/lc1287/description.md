# Element Appearing More Than 25% In Sorted Array

Given an integer array **sorted** in non-decreasing order, there is exactly one integer in the array that occurs more than 25% of the time, return that integer.

## Example 1:

> **Input:** arr = [1,2,2,6,6,6,6,7,10]
> **Output:** 6

## Example 2:

> **Input:** arr = [1,1]
> **Output:** 1

## Constraints:

- `1 <= arr.length <= 10^4`
- `0 <= arr[i] <= 10^5`

## Starter Code

```dafny
predicate find_special_integer_pre(arr: seq<int>)

predicate find_special_integer_post(arr: seq<int>, res: int)
  requires find_special_integer_pre(arr)

method find_special_integer(arr: seq<int>) returns (res: int)
  requires find_special_integer_pre(arr)
  ensures find_special_integer_post(arr, res)
```
