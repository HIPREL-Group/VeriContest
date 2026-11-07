# Paint Fence

There is a fence with `n` posts, and each post can be painted with one of the `k` colors.

You have to paint all the posts such that no more than two adjacent fence posts have the same color.

Return the number of ways you can paint the fence.

## Example 1:

> **Input:** n = 3, k = 2
> **Output:** 6

## Example 2:

> **Input:** n = 1, k = 1
> **Output:** 1

## Constraints:

- $0 <= n <= 50$
- $1 <= k <= 10^5$
- The answer is guaranteed to fit in a 32-bit signed integer.

## Starter Code

```dafny
predicate num_ways_pre(n: int, k: int)

predicate num_ways_post(n: int, k: int, res: int)
  requires num_ways_pre(n, k)

method num_ways(n: int, k: int) returns (res: int)
  requires num_ways_pre(n, k)
  ensures num_ways_post(n, k, res)
```
