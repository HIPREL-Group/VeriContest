# Maximum Area of a Piece of Cake After Horizontal and Vertical Cuts

You are given a rectangular cake of size `h x w` and two arrays of integers `horizontalCuts` and `verticalCuts` where:

- `horizontalCuts[i]` is the distance from the top of the rectangular cake to the `i`th horizontal cut and similarly,
- `verticalCuts[j]` is the distance from the left of the rectangular cake to the `j`th vertical cut.

Return the maximum area of a piece of cake after you cut at each horizontal and vertical position provided in the arrays `horizontalCuts` and `verticalCuts`. Since the answer can be a large number, return this **modulo** $10^9 + 7$.

## Example 1:

> **Input:** h = 5, w = 4, horizontalCuts = [1,2,4], verticalCuts = [1,3]
> **Output:** 4
> **Explanation:** The figure above represents the given rectangular cake. Red lines are the horizontal and vertical cuts. After you cut the cake, the green piece of cake has the maximum area.

## Example 2:

> **Input:** h = 5, w = 4, horizontalCuts = [3,1], verticalCuts = [1]
> **Output:** 6
> **Explanation:** The figure above represents the given rectangular cake. Red lines are the horizontal and vertical cuts. After you cut the cake, the green and yellow pieces of cake have the maximum area.

## Example 3:

> **Input:** h = 5, w = 4, horizontalCuts = [3], verticalCuts = [3]
> **Output:** 9

## Constraints:

- $2 \leq h, w \leq 10^9$
- $1 \leq$ `horizontalCuts.length` $\leq \min(h - 1, 10^5)$
- $1 \leq$ `verticalCuts.length` $\leq \min(w - 1, 10^5)$
- $1 \leq$ `horizontalCuts[i]` $< h$
- $1 \leq$ `verticalCuts[j]` $< w$
- All the elements in `horizontalCuts` are distinct.
- All the elements in `verticalCuts` are distinct.

## Starter Code

```rust
impl Solution {
    pub fn max_area(h: i32, w: i32, horizontal_cuts: Vec<i32>, vertical_cuts: Vec<i32>) -> i32 {
        
    }
}
```
