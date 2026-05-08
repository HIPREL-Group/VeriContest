# Online Majority Element In Subarray

Given an array `arr`, find the **majority element** of a given subarray. The **majority element** of a subarray is an element that occurs `threshold` times or more in the subarray.

Given `arr`, `left`, `right`, and `threshold`, return the element in the subarray `arr[left...right]` that occurs at least `threshold` times, or `-1` if no such element exists.

## Example 1:

> **Input:** arr = [1, 1, 2, 2, 1, 1], left = 0, right = 5, threshold = 4
> **Output:** 1

## Example 2:

> **Input:** arr = [1, 1, 2, 2, 1, 1], left = 0, right = 3, threshold = 3
> **Output:** -1

## Example 3:

> **Input:** arr = [1, 1, 2, 2, 1, 1], left = 2, right = 3, threshold = 2
> **Output:** 2

## Constraints:

- $1 \leq arr.length \leq 2 * 10^4$
- $1 \leq arr[i] \leq 2 * 10^4$
- $0 \leq left \leq right < arr.length$
- $threshold \leq right - left + 1$
- $2 * threshold > right - left + 1$

## Starter Code

```rust
struct MajorityChecker {

}


/** 
 * `&self` means the method takes an immutable reference.
 * If you need a mutable reference, change it to `&mut self` instead.
 */
impl MajorityChecker {

    fn new(arr: Vec<i32>) -> Self {
        
    }
    
    fn query(&self, left: i32, right: i32, threshold: i32) -> i32 {
        
    }
}

/**
 * Your MajorityChecker object will be instantiated and called as such:
 * let obj = MajorityChecker::new(arr);
 * let ret_1: i32 = obj.query(left, right, threshold);
 */
```
