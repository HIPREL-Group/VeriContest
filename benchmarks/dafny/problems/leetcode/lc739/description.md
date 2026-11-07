# Daily Temperatures

You are given an array of integers `temperatures` representing the daily temperatures.

Return an array `answer` such that `answer[i]` is the number of days you have to wait after the $i^{th}$ day to get a warmer temperature. If there is no future day for which this is possible, keep `answer[i] == 0` instead.

## Example 1:

> **Input:** temperatures = [73,74,75,71,69,72,76,73]
> **Output:** [1,1,4,2,1,1,0,0]

## Example 2:

> **Input:** temperatures = [30,40,50,60]
> **Output:** [1,1,1,0]

## Example 3:

> **Input:** temperatures = [30,60,90]
> **Output:** [1,1,0]

## Constraints:

- $1 <= temperatures.length <= 10^5$
- $30 <= temperatures[i] <= 100$

## Starter Code

```dafny
predicate daily_temperatures_pre(temperatures: seq<int>)

predicate daily_temperatures_post(temperatures: seq<int>, res: seq<int>)
  requires daily_temperatures_pre(temperatures)

method daily_temperatures(temperatures: seq<int>) returns (res: seq<int>)
  requires daily_temperatures_pre(temperatures)
  ensures daily_temperatures_post(temperatures, res)
```
