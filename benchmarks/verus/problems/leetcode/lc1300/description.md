# Sum of Mutated Array Closest to Target

Given an integer array `arr` and a target value `target`, return the integer `value` such that when we change all the integers larger than `value` in the given array to be equal to `value`, the sum of the array gets as close as possible (in absolute difference) to `target`.

In case of a tie, return the minimum such integer.

Notice that the answer is not necessarily a number from `arr`.

## Example 1:

> **Input:** arr = [4,9,3], target = 10
> **Output:** 3
> **Explanation:** When using 3 arr converts to [3, 3, 3] which sums 9 and that's the optimal answer.

## Example 2:

> **Input:** arr = [2,3,5], target = 10
> **Output:** 5

## Example 3:

> **Input:** arr = [60864,25176,27249,21296,20204], target = 56803
> **Output:** 11361

## Constraints:

- $1 \leq \text{arr.length} \leq 10^4$
- $1 \leq \text{arr}[i], \text{target} \leq 10^5$

## Starter Code

```rust
impl Solution {
    pub fn find_best_value(arr: Vec<i32>, target: i32) -> i32 {
        
    }
}
```
