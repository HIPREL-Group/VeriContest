# Find Positive Integer Solution for a Given Equation

Given a callable function `f(x, y)` **with a hidden formula** and a value `z`, reverse engineer the formula and return *all positive integer pairs* `x` *and* `y` *where* `f(x,y) == z`. You may return the pairs in any order.

While the exact formula is hidden, the function is monotonically increasing, i.e.:

- `f(x, y) < f(x + 1, y)`
- `f(x, y) < f(x, y + 1)`

The function interface is defined like this:

```
interface CustomFunction {
public:
  // Returns some positive integer f(x, y) for two positive integers x and y based on a formula.
  int f(int x, int y);
};
```

We will judge your solution as follows:

- The judge has a list of `9` hidden implementations of `CustomFunction`, along with a way to generate an **answer key** of all valid pairs for a specific `z`.
- The judge will receive two inputs: a `function_id` (to determine which implementation to test your code with), and the target `z`.
- The judge will call your `findSolution` and compare your results with the **answer key**.
- If your results match the **answer key**, your solution will be `Accepted`.

## Example 1:

> **Input:** function_id = 1, z = 5
> **Output:** [[1,4],[2,3],[3,2],[4,1]]
> **Explanation:** The hidden formula for function_id = 1 is f(x, y) = x + y.

## Example 2:

> **Input:** function_id = 2, z = 5
> **Output:** [[1,5],[5,1]]
> **Explanation:** The hidden formula for function_id = 2 is f(x, y) = x * y.

## Constraints:

- `1 <= function_id <= 9`
- `1 <= z <= 100`
- It is guaranteed that the solutions of `f(x, y) == z` will be in the range `1 <= x, y <= 1000`.
- It is also guaranteed that `f(x, y)` will fit in 32 bit signed integer if `1 <= x, y <= 1000`.

## Starter Code

```rust
/*
 * // This is the custom function interface.
 * // You should not implement it, or speculate about its implementation
 * struct CustomFunction;
 * impl CustomFunction {
 *    pub fn f(x:i32,y:i32)->i32{}
 * }
 */

impl Solution {
    pub fn find_solution(customfunction: &CustomFunction, z: i32) -> Vec<Vec<i32>> {
	
    }
}
```
