# Unique Binary Search Trees

Given an integer `n`, return the number of structurally unique BSTs which have exactly `n` nodes of unique values from 1 to n.

## Example 1:

> **Input:** n = 3
> **Output:** 5

## Example 2:

> **Input:** n = 1
> **Output:** 1

## Constraints:

- $1 \leq$ `n` $\leq 19$

## Starter Code

```dafny
predicate num_trees_pre(n: int)

predicate num_trees_post(n: int, result: int)
  requires num_trees_pre(n)

method num_trees(n: int) returns (result: int)
  requires num_trees_pre(n)
  ensures num_trees_post(n, result)
```
