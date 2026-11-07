# 118. Pascal's Triangle
Given an integer `numRows`, return the first `numRows` of **Pascal's triangle**.  
In **Pascal's triangle**, each number is the sum of the two numbers directly above it as shown:

![Pascal's Triangle Animation](PascalTriangleAnimated2.gif)

## Example 1:

```
Input: numRows = 5
Output: [[1],[1,1],[1,2,1],[1,3,3,1],[1,4,6,4,1]]
```

## Example 2:

```
Input: numRows = 1
Output: [[1]]
```

## Constraints:

- `1 <= numRows <= 30`

## Starter Code

```dafny
predicate generate_pre(num_rows: int)

predicate generate_post(num_rows: int, triangle: seq<seq<int>>)
  requires generate_pre(num_rows)

method generate(num_rows: int) returns (triangle: seq<seq<int>>)
  requires generate_pre(num_rows)
  ensures generate_post(num_rows, triangle)
```
