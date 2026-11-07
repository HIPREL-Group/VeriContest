# Koko Eating Bananas

Koko loves to eat bananas. There are `n` piles of bananas, and the `i^th` pile has `piles[i]` bananas. The guards have gone and will come back in `h` hours.

Koko can decide her bananas-per-hour eating speed of `k`. Each hour, she chooses some pile of bananas and eats `k` bananas from that pile. If the pile has fewer than `k` bananas, she eats all of them instead and does not eat any more bananas during that hour.

Koko likes to eat slowly but still wants to finish eating all the bananas before the guards return.

Return the minimum integer `k` such that she can eat all the bananas within `h` hours.

## Example 1:

> **Input:** piles = [3,6,7,11], h = 8
> **Output:** 4

## Example 2:

> **Input:** piles = [30,11,23,4,20], h = 5
> **Output:** 30

## Example 3:

> **Input:** piles = [30,11,23,4,20], h = 6
> **Output:** 23

## Constraints:

- `1 <= piles.length <= 10^4`
- `piles.length <= h <= 10^9`
- `1 <= piles[i] <= 10^9`

## Starter Code

```dafny
predicate min_eating_speed_pre(piles: seq<int>, h: int)

predicate min_eating_speed_post(piles: seq<int>, h: int, res: int)
  requires min_eating_speed_pre(piles, h)

method min_eating_speed(piles: seq<int>, h: int) returns (res: int)
  requires min_eating_speed_pre(piles, h)
  ensures min_eating_speed_post(piles, h, res)
```
