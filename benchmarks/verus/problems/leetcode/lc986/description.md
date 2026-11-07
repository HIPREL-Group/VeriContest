# Interval List Intersections

You are given two lists of closed intervals, `firstList` and `secondList`, where `firstList[i] = [start_i, end_i]` and `secondList[j] = [start_j, end_j]`. Each list of intervals is pairwise **disjoint** and in **sorted order**.

Return the intersection of these two interval lists.

A **closed interval** $[a, b]$ (with $a <= b$) denotes the set of real numbers $x$ with $a <= x <= b$.

The **intersection** of two closed intervals is a set of real numbers that are either empty or represented as a closed interval. For example, the intersection of [1, 3] and [2, 4] is [2, 3].

## Example 1:

> **Input:** firstList = [[0,2],[5,10],[13,23],[24,25]], secondList = [[1,5],[8,12],[15,24],[25,26]]
> **Output:** [[1,2],[5,5],[8,10],[15,23],[24,24],[25,25]]

## Example 2:

> **Input:** firstList = [[1,3],[5,9]], secondList = []
> **Output:** []

## Constraints:

- $0 <= firstList.length, secondList.length <= 1000$
- $firstList.length + secondList.length >= 1$
- $0 <= start_i < end_i <= 10^9$
- $end_i < start_{i+1}$
- $0 <= start_j < end_j <= 10^9$
- $end_j < start_{j+1}$

## Starter Code

```rust
impl Solution {
    pub fn interval_intersection(first_list: Vec<Vec<i32>>, second_list: Vec<Vec<i32>>) -> Vec<Vec<i32>> {
        
    }
}
```
