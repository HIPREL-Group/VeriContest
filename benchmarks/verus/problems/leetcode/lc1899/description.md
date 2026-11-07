# Merge Triplets to Form Target Triplet

A triplet is an array of three integers. You are given a 2D integer array `triplets`, where `triplets[i] = [a_i, b_i, c_i]` describes the $i^{th}$ triplet. You are also given an integer array `target = [x, y, z]` that describes the triplet you want to obtain.

To obtain `target`, you may apply the following operation on `triplets` any number of times:

- Choose two indices `i` and `j` (`i != j`) and update `triplets[j]` to become `[max(a_i, a_j), max(b_i, b_j), max(c_i, c_j)]`.

For example, if `triplets[i] = [2, 5, 3]` and `triplets[j] = [1, 7, 5]`, then `triplets[j]` becomes `[max(2, 1), max(5, 7), max(3, 5)] = [2, 7, 5]`.

Return `true` if it is possible to obtain `target` as an element of `triplets`, or `false` otherwise.

## Example 1:

> **Input:** triplets = [[2,5,3],[1,8,4],[1,7,5]], target = [2,7,5]
> **Output:** true
> **Explanation:** Choose the first and last triplets and update the last triplet to `[2,7,5]`. The target triplet is then an element of `triplets`.

## Example 2:

> **Input:** triplets = [[3,4,5],[4,5,6]], target = [3,2,5]
> **Output:** false
> **Explanation:** It is impossible to obtain `[3,2,5]` because no triplet contains `2` in the second position.

## Example 3:

> **Input:** triplets = [[2,5,3],[2,3,4],[1,2,5],[5,2,3]], target = [5,5,5]
> **Output:** true
> **Explanation:** Merge the first and third triplets to obtain `[2,5,5]`, then merge that result with the fourth triplet to obtain `[5,5,5]`.

## Constraints:

- $1 <= triplets.length <= 10^5$
- $triplets[i].length == target.length == 3$
- $1 <= a_i, b_i, c_i, x, y, z <= 1000$

## Starter Code

```rust
impl Solution {
    pub fn merge_triplets(triplets: Vec<Vec<i32>>, target: Vec<i32>) -> bool {
        
    }
}
```
