# Fruits Into Baskets II

You are given two integer arrays, `fruits` and `baskets`, each of length `n`, where:

- `fruits[i]` is the quantity of the `i`th type of fruit.
- `baskets[j]` is the capacity of the `j`th basket.

From left to right, place the fruits according to these rules:

- Each fruit type must be placed in the leftmost available basket whose capacity is at least that fruit quantity.
- Each basket can hold only one type of fruit.
- If a fruit type cannot be placed in any basket, it remains unplaced.

Return the number of fruit types that remain unplaced after all possible placements.

## Example 1:

> **Input:** fruits = [4,2,5], baskets = [3,5,4]
> **Output:** 1
>
> **Explanation:**
>
> - `fruits[0] = 4` is placed in `baskets[1] = 5`.
> - `fruits[1] = 2` is placed in `baskets[0] = 3`.
> - `fruits[2] = 5` cannot be placed in `baskets[2] = 4`.

## Example 2:

> **Input:** fruits = [3,6,1], baskets = [6,4,7]
> **Output:** 0
>
> **Explanation:**
>
> - `fruits[0] = 3` is placed in `baskets[0] = 6`.
> - `fruits[1] = 6` is placed in `baskets[2] = 7`.
> - `fruits[2] = 1` is placed in `baskets[1] = 4`.

## Constraints:

- `n == fruits.length == baskets.length`
- `1 <= n <= 100`
- `1 <= fruits[i], baskets[i] <= 1000`

## Starter Code

```dafny
predicate num_of_unplaced_fruits_pre(fruits: seq<int>, baskets: seq<int>)

predicate num_of_unplaced_fruits_post(fruits: seq<int>, baskets: seq<int>, result: int)
  requires num_of_unplaced_fruits_pre(fruits, baskets)

method num_of_unplaced_fruits(fruits: seq<int>, baskets: seq<int>) returns (result: int)
  requires num_of_unplaced_fruits_pre(fruits, baskets)
  ensures num_of_unplaced_fruits_post(fruits, baskets, result)
```
