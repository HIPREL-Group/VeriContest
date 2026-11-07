# Find Missing Observations

You have results from `n + m` rolls of a standard 6-sided die, but `n` of the rolls are missing. You are given the remaining `m` observed rolls in `rolls`, along with the overall integer mean of all `n + m` rolls.

Return an array of length `n` containing any valid values for the missing rolls so that the mean of all `n + m` rolls is exactly `mean`. If no such array exists, return an empty array.

## Example 1:

> **Input:** rolls = [3, 2, 4, 3], mean = 4, n = 2
> **Output:** [6, 6]
> **Explanation:** The mean of all 6 rolls is $(3 + 2 + 4 + 3 + 6 + 6) / 6 = 4$.

## Example 2:

> **Input:** rolls = [1, 5, 6], mean = 3, n = 4
> **Output:** [2, 3, 2, 2]
> **Explanation:** The mean of all 7 rolls is $(1 + 5 + 6 + 2 + 3 + 2 + 2) / 7 = 3$.

## Example 3:

> **Input:** rolls = [1, 2, 3, 4], mean = 6, n = 4
> **Output:** []
> **Explanation:** No choice of 4 missing rolls can make the overall mean equal to 6.

## Constraints:

- $m == \texttt{rolls.length}$
- $1 \leq n, m \leq 10^5$
- $1 \leq \texttt{rolls}[i], \texttt{mean} \leq 6$

## Starter Code

```dafny
predicate missing_rolls_pre(rolls: seq<int>, mean: int, n: int)

predicate missing_rolls_post(rolls: seq<int>, mean: int, n: int, res: seq<int>)
  requires missing_rolls_pre(rolls, mean, n)

method missing_rolls(rolls: seq<int>, mean: int, n: int) returns (res: seq<int>)
  requires missing_rolls_pre(rolls, mean, n)
  ensures missing_rolls_post(rolls, mean, n, res)
```
