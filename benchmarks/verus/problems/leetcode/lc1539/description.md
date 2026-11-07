# Kth Missing Positive Number

Given an array `arr` of positive integers sorted in a **strictly increasing order**, and an integer `k`, return the $k$th positive integer that is missing from this array.

## Example 1:

> **Input:** arr = [2,3,4,7,11], k = 5
> **Output:** 9
> **Explanation:** The missing positive integers are [1,5,6,8,9,...]. The 5th missing positive integer is 9.

## Example 2:

> **Input:** arr = [1,2,3,4], k = 2
> **Output:** 6
> **Explanation:** The missing positive integers are [5,6,7,...]. The 2nd missing positive integer is 6.

## Constraints:

- $1 \leq arr.length \leq 1000$
- $1 \leq arr[i] \leq 1000$
- $1 \leq k \leq 1000$
- `arr` is sorted in strictly increasing order.

## Follow up:

Could you solve this problem in less than $O(n)$ complexity?

## Starter Code

```rust
impl Solution {
    pub fn find_kth_positive(arr: Vec<i32>, k: i32) -> i32 {
        
    }
}
```
