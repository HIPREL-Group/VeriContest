# Lexicographical Numbers

Given an integer `n`, return all the numbers in the range `[1, n]` sorted in lexicographical order.

You must write an algorithm that runs in `O(n)` time and uses `O(1)` extra space.

## Example 1:

> **Input:** n = 13
> **Output:** [1,10,11,12,13,2,3,4,5,6,7,8,9]

## Example 2:

> **Input:** n = 2
> **Output:** [1,2]

## Constraints:

- $1 \leq n \leq 5 \times 10^4$

## Starter Code

```dafny
predicate lexical_order_pre(n: int)

predicate lexical_order_post(n: int, result: seq<int>)
  requires lexical_order_pre(n)

method lexical_order(n: int) returns (result: seq<int>)
  requires lexical_order_pre(n)
  ensures lexical_order_post(n, result)
```
