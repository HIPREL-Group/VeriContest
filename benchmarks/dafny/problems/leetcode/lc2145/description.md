# Count the Hidden Sequences

You are given a 0-indexed array of `n` integers `differences`, where
`differences[i] = hidden[i + 1] - hidden[i]` for a hidden sequence `hidden` of
length `n + 1`.

You are also given two integers `lower` and `upper`, describing the inclusive
range `[lower, upper]` that every value in `hidden` must lie within.

Return the number of possible hidden sequences. If there are no possible
sequences, return `0`.

## Example 1:

> **Input:** differences = [1, -3, 4], lower = 1, upper = 6
> **Output:** 2
> **Explanation:** The possible hidden sequences are [3, 4, 1, 5] and [4, 5, 2, 6].

## Example 2:

> **Input:** differences = [3, -4, 5, 1, -2], lower = -4, upper = 5
> **Output:** 4

## Example 3:

> **Input:** differences = [4, -7, 2], lower = 3, upper = 6
> **Output:** 0

## Constraints:

- `n == differences.length`
- `1 <= n <= 10^5`
- `-10^5 <= differences[i] <= 10^5`
- `-10^5 <= lower <= upper <= 10^5`

## Starter Code

```dafny
predicate number_of_arrays_pre(differences: seq<int>, lower: int, upper: int)

predicate number_of_arrays_post(differences: seq<int>, lower: int, upper: int, result: int)
  requires number_of_arrays_pre(differences, lower, upper)

method number_of_arrays(differences: seq<int>, lower: int, upper: int) returns (result: int)
  requires number_of_arrays_pre(differences, lower, upper)
  ensures number_of_arrays_post(differences, lower, upper, result)
```
