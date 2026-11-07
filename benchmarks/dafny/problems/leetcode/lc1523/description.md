# Count Odd Numbers in an Interval Range

Given two non-negative integers `low` and `high`, return the count of odd numbers between `low` and `high` (inclusive).

## Example 1:

> **Input:** low = 3, high = 7
> **Output:** 3
> **Explanation:** The odd numbers between 3 and 7 are [3,5,7].

## Example 2:

> **Input:** low = 8, high = 10
> **Output:** 1
> **Explanation:** The odd numbers between 8 and 10 are [9].

## Constraints:

- $0 \leq low \leq high \leq 10^9$

## Starter Code

```dafny
predicate count_odds_pre(low: int, high: int)

predicate count_odds_post(low: int, high: int, res: int)
  requires count_odds_pre(low, high)

method count_odds(low: int, high: int) returns (res: int)
  requires count_odds_pre(low, high)
  ensures count_odds_post(low, high, res)
```
