# Peak Index in a Mountain Array

An array `arr` is a **mountain** if the following properties hold:

- `arr.length >= 3`
- There exists some `i` with `0 < i < arr.length - 1` such that:
  - `arr[0] < arr[1] < ... < arr[i - 1] < arr[i]`
  - `arr[i] > arr[i + 1] > ... > arr[arr.length - 1]`

Given a mountain array `arr`, return the index `i` such that the above conditions hold (i.e., the peak index).

## Example 1:

> **Input:** arr = [0,1,0]
> **Output:** 1

## Example 2:

> **Input:** arr = [0,2,1,0]
> **Output:** 1

## Example 3:

> **Input:** arr = [0,10,5,2]
> **Output:** 1

You must write an algorithm that runs in $O(\log n)$ time.

## Constraints:

- $3 \leq arr.length \leq 10^5$

- $0 \leq arr[i] \leq 10^6$

- `arr` is guaranteed to be a mountain array.

## Starter Code

```rust
impl Solution {
    pub fn peak_index_in_mountain_array(arr: Vec<i32>) -> i32 {
        
    }
}
```
