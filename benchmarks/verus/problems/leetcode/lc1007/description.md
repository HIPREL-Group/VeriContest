# Minimum Domino Rotations For Equal Row

In a row of dominoes, `tops[i]` and `bottoms[i]` represent the top and bottom halves of the `i`th domino. (A domino is a tile with two numbers from 1 to 6 - one on each half of the tile.)

We may rotate the `i`th domino, so that `tops[i]` and `bottoms[i]` swap values.

Return the minimum number of rotations so that all the values in `tops` are the same, or all the values in `bottoms` are the same.

If it cannot be done, return `-1`.

## Example 1:

> **Input:** tops = [2,1,2,4,2,2], bottoms = [5,2,6,2,3,2]
> **Output:** 2
> **Explanation:** If we rotate the second and fourth dominoes, we can make every value in the top row equal to 2.

## Example 2:

> **Input:** tops = [3,5,1,2,3], bottoms = [3,6,3,3,4]
> **Output:** -1
> **Explanation:** In this case, it is not possible to rotate the dominoes to make one row of values equal.

## Constraints:

- $2 \leq tops.length \leq 2 \times 10^4$
- $bottoms.length == tops.length$
- $1 \leq tops[i], bottoms[i] \leq 6$

## Starter Code

```rust
impl Solution {
    pub fn min_domino_rotations(tops: Vec<i32>, bottoms: Vec<i32>) -> i32 {
        
    }
}
```
