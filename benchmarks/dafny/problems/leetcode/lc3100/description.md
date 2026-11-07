# Water Bottles II

You are given two integers `numBottles` and `numExchange`.

`numBottles` is the number of full water bottles you initially have. In one operation, you can:

- Drink any number of full bottles, turning them into empty bottles.
- Exchange `numExchange` empty bottles for one full bottle, then increase `numExchange` by `1`.

You cannot exchange multiple batches using the same `numExchange` value in a single step.

Return the maximum number of water bottles you can drink.

## Example 1:

> **Input:** numBottles = 13, numExchange = 6  
> **Output:** 15

## Example 2:

> **Input:** numBottles = 10, numExchange = 3  
> **Output:** 13

## Constraints:

- `1 <= numBottles <= 100`
- `1 <= numExchange <= 100`

## Starter Code

```dafny
predicate max_bottles_drunk_pre(num_bottles: int, num_exchange: int)

predicate max_bottles_drunk_post(num_bottles: int, num_exchange: int, result: int)
  requires max_bottles_drunk_pre(num_bottles, num_exchange)

method max_bottles_drunk(num_bottles: int, num_exchange: int) returns (result: int)
  requires max_bottles_drunk_pre(num_bottles, num_exchange)
  ensures max_bottles_drunk_post(num_bottles, num_exchange, result)
```
