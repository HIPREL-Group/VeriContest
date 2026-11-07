# Valid Mountain Array

Given an array of integers `arr`, return `true` if and only if it is a valid mountain array.

Recall that `arr` is a mountain array if and only if:

- `arr.length >= 3`
- There exists some `i` with `0 < i < arr.length - 1` such that:
  - `arr[0] < arr[1] < ... < arr[i - 1] < arr[i]`
  - `arr[i] > arr[i + 1] > ... > arr[arr.length - 1]`

## Example 1:

> **Input:** arr = [2,1]
> **Output:** false

## Example 2:

> **Input:** arr = [3,5,5]
> **Output:** false

## Example 3:

> **Input:** arr = [0,3,2,1]
> **Output:** true

## Constraints:

- $1 <= arr.length <= 10^4$

- $0 <= arr[i] <= 10^4$

## Starter Code

```dafny
predicate valid_mountain_array_pre(arr: seq<int>)

predicate valid_mountain_array_post(arr: seq<int>, result: bool)
  requires valid_mountain_array_pre(arr)

method valid_mountain_array(arr: seq<int>) returns (result: bool)
  requires valid_mountain_array_pre(arr)
  ensures valid_mountain_array_post(arr, result)
```
