# Alternating Groups I

There is a circle of red and blue tiles. You are given an array of integers `colors`. The color of tile `i` is represented by `colors[i]`:

- `colors[i] == 0` means that tile `i` is **red**.
- `colors[i] == 1` means that tile `i` is **blue**.

Every 3 **contiguous** tiles in the circle with **alternating** colors (the middle tile has a different color from its left and right tiles) is called an **alternating group**.

Return the number of **alternating groups**.

**Note** that since `colors` represents a circle, the first and the last tiles are considered to be next to each other.

## Examples

**Example 1:**
Input: colors = [1,1,1]
Output: 0

**Example 2:**
Input: colors = [0,1,0,0,1]
Output: 3
Explanation:
Alternating groups: colors[2] with neighbors colors[1] and colors[3], colors[0] with neighbors colors[4] and colors[1], colors[4] with neighbors colors[3] and colors[0].

## Constraints

- 3 <= colors.length <= 100
- 0 <= colors[i] <= 1

## Starter Code

```dafny
predicate number_of_alternating_groups_pre(colors: seq<int>)

predicate number_of_alternating_groups_post(colors: seq<int>, result: int)
  requires number_of_alternating_groups_pre(colors)

method number_of_alternating_groups(colors: seq<int>) returns (result: int)
  requires number_of_alternating_groups_pre(colors)
  ensures number_of_alternating_groups_post(colors, result)
```
