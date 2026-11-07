# 119. Pascal's Triangle II
Given an integer `rowIndex`, return the `rowIndex`th (**0-indexed**) row of **Pascal's triangle**.

In **Pascal's triangle**, each number is the sum of the two numbers directly above it as shown:

![Pascal's Triangle Animation](PascalTriangleAnimated2.gif)

## Example 1:

```
Input: rowIndex = 3
Output: [1,3,3,1]
```

## Example 2:

```
Input: rowIndex = 0
Output: [1]
```

## Example 3:

```
Input: rowIndex = 1
Output: [1,1]
```

## Constraints:

- `0 <= numRows <= 33`

**Follow up**: Could you optimize your algorithm to use only `O(rowIndex)` extra space?

## Starter Code

```dafny
predicate get_row_pre(row_index: int)

predicate get_row_post(row_index: int, row: seq<int>)
  requires get_row_pre(row_index)

method get_row(row_index: int) returns (row: seq<int>)
  requires get_row_pre(row_index)
  ensures get_row_post(row_index, row)
```
