# Partition Array Into Three Parts With Equal Sum

Given an array of integers `arr`, return `true` if it can be partitioned into three non-empty parts with equal sums.

Formally, the array can be partitioned if there exist indices `i + 1 < j` such that

`arr[0] + arr[1] + ... + arr[i] == arr[i + 1] + arr[i + 2] + ... + arr[j - 1] == arr[j] + arr[j + 1] + ... + arr[arr.length - 1]`.

## Example 1:

> **Input:** arr = [0,2,1,-6,6,-7,9,1,2,0,1]
> **Output:** true
> **Explanation:** 0 + 2 + 1 = -6 + 6 - 7 + 9 + 1 = 2 + 0 + 1

## Example 2:

> **Input:** arr = [0,2,1,-6,6,7,9,-1,2,0,1]
> **Output:** false

## Example 3:

> **Input:** arr = [3,3,6,5,-2,2,5,1,-9,4]
> **Output:** true
> **Explanation:** 3 + 3 = 6 = 5 - 2 + 2 + 5 + 1 - 9 + 4

## Constraints:

- `3 <= arr.length <= 5 * 10^4`
- `-10^4 <= arr[i] <= 10^4`

## Starter Code

```rust
impl Solution {
    pub fn can_three_parts_equal_sum(arr: Vec<i32>) -> bool {
        
    }
}
```
