# Three Consecutive Odds

Given an integer array `arr`, return `true` if there are three consecutive odd numbers in the array. Otherwise, return `false`.

## Example 1:
> **Input:** arr = [2,6,4,1]
> **Output:** false
> **Explanation:**
> There are no three consecutive odds.

## Example 2:
> **Input:** arr = [1,2,34,3,4,5,7,23,12]
> **Output:** true
> **Explanation:**
> [5,7,23] are three consecutive odds.

## Constraints:

- $1 \leq arr.length \leq 1000$

- $1 \leq arr[i] \leq 1000$

## Starter Code

```dafny
predicate three_consecutive_odds_pre(arr: seq<int>)

predicate three_consecutive_odds_post(arr: seq<int>, result: bool)
  requires three_consecutive_odds_pre(arr)

method three_consecutive_odds(arr: seq<int>) returns (result: bool)
  requires three_consecutive_odds_pre(arr)
  ensures three_consecutive_odds_post(arr, result)
```
