# 258. Add Digits

Given an integer `num`, repeatedly add all its digits until the result has only one digit, and return it.

## Example 1:

```
Input: num = 38
Output: 2
Explanation: The process is
38 --> 3 + 8 --> 11
11 --> 1 + 1 --> 2 
Since 2 has only one digit, return it.
```

## Example 2:

```
Input: num = 0
Output: 0
```

## Constraints:

- $0 <= numRows <= 2*{31} - 1$

**Follow up**: Could you do it without any loop/recursion in `O(1)` runtime?

## Starter Code

```dafny
predicate add_digits_pre(n: int)

predicate add_digits_post(n: int, result: int)
  requires add_digits_pre(n)

method add_digits(n: int) returns (result: int)
  requires add_digits_pre(n)
  ensures add_digits_post(n, result)
```
