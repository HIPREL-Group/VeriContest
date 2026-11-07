# Find Closest Person

You are given three integers `x`, `y`, and `z`, representing the positions of three people on a number line:

- `x` is the position of Person 1.
- `y` is the position of Person 2.
- `z` is the position of Person 3, who does not move.

Both Person 1 and Person 2 move toward Person 3 at the same speed.

Return:

- `1` if Person 1 reaches Person 3 first.
- `2` if Person 2 reaches Person 3 first.
- `0` if both reach Person 3 at the same time.

## Example 1:

> **Input:** x = 2, y = 7, z = 4
> **Output:** 1

## Example 2:

> **Input:** x = 2, y = 5, z = 6
> **Output:** 2

## Example 3:

> **Input:** x = 1, y = 5, z = 3
> **Output:** 0

## Constraints:

- `1 <= x, y, z <= 100`

## Starter Code

```dafny
predicate find_closest_pre(x: int, y: int, z: int)

predicate find_closest_post(x: int, y: int, z: int, result: int)
  requires find_closest_pre(x, y, z)

method find_closest(x: int, y: int, z: int) returns (result: int)
  requires find_closest_pre(x, y, z)
  ensures find_closest_post(x, y, z, result)
```
