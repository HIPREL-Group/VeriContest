# Most Frequent Prime

You are given an `m x n` 0-indexed 2D matrix `mat`. From every cell, you can create numbers in the following way:

- There are at most 8 paths from the cell: east, south-east, south, south-west, west, north-west, north, and north-east.
- Select one path and append digits along that path to the number being formed.
- Numbers are generated at every step. For example, for digits `1, 9, 1`, the generated numbers are `1`, `19`, `191`.

Return the most frequent prime number greater than `10` among all numbers created by traversing the matrix, or `-1` if no such prime exists. If multiple primes have the same highest frequency, return the largest one.

**Note:** You cannot change direction while moving.

## Example 1:

> **Input:** mat = [[1,1],[9,9],[1,1]]
> **Output:** 19

## Example 2:

> **Input:** mat = [[7]]
> **Output:** -1
> **Explanation:** The only number formed is 7, which is prime but not greater than 10.

## Example 3:

> **Input:** mat = [[9,7,8],[4,6,5],[2,8,6]]
> **Output:** 97

## Constraints:

- `m == mat.length`
- `n == mat[i].length`
- `1 <= m, n <= 6`
- `1 <= mat[i][j] <= 9`

## Starter Code

```rust
impl Solution {
    pub fn most_frequent_prime(mat: Vec<Vec<i32>>) -> i32 {
        
    }
}
```
