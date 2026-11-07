# Maximum Containers on a Ship

You are given positive integers `n`, `w`, and `maxWeight`.

There is an `n x n` cargo deck on a ship. Each cell can hold one container, and each container weighs exactly `w`.

The total weight of loaded containers must be at most `maxWeight`.

Return the maximum number of containers that can be loaded.

## Example 1:

> **Input:** n = 2, w = 3, maxWeight = 15  
> **Output:** 4  
> **Explanation:** The deck has 4 cells. Loading all 4 containers weighs 12, which is within `maxWeight`.

## Example 2:

> **Input:** n = 3, w = 5, maxWeight = 20  
> **Output:** 4  
> **Explanation:** The deck has 9 cells, but 5 containers would weigh 25. So the maximum feasible number is 4.

## Constraints:

- `1 <= n <= 1000`
- `1 <= w <= 1000`
- `1 <= maxWeight <= 10^9`

## Starter Code

```dafny
predicate max_containers_pre(n: int, w: int, max_weight: int)

predicate max_containers_post(n: int, w: int, max_weight: int, result: int)
  requires max_containers_pre(n, w, max_weight)

method max_containers(n: int, w: int, max_weight: int) returns (result: int)
  requires max_containers_pre(n, w, max_weight)
  ensures max_containers_post(n, w, max_weight, result)
```
