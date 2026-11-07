# Find Good Days to Rob the Bank

You and a gang of thieves are planning on robbing a bank. You are given a 0-indexed integer array `security`, where `security[i]` is the number of guards on duty on the `i^th` day. The days are numbered starting from `0`. You are also given an integer `time`.

The `i^th` day is a good day to rob the bank if:

- There are at least `time` days before and after the `i^th` day.
- The number of guards for the `time` days before `i` is non-increasing.
- The number of guards for the `time` days after `i` is non-decreasing.

More formally, day `i` is good if and only if
`security[i - time] >= security[i - time + 1] >= ... >= security[i] <= ... <= security[i + time - 1] <= security[i + time]`.

Return a list of all days that are good days to rob the bank. The order of the returned days does not matter.

## Example 1:

> **Input:** security = [5,3,3,3,5,6,2], time = 2
> **Output:** [2,3]
> **Explanation:** On day 2, we have `security[0] >= security[1] >= security[2] <= security[3] <= security[4]`.
> On day 3, we have `security[1] >= security[2] >= security[3] <= security[4] <= security[5]`.
> No other day satisfies the condition.

## Example 2:

> **Input:** security = [1,1,1,1,1], time = 0
> **Output:** [0,1,2,3,4]
> **Explanation:** Since `time = 0`, every day is a good day.

## Example 3:

> **Input:** security = [1,2,3,4,5,6], time = 2
> **Output:** []
> **Explanation:** No day has 2 days before it with a non-increasing number of guards.

## Constraints:

- `1 <= security.length <= 10^5`
- `0 <= security[i], time <= 10^5`

## Starter Code

```rust
impl Solution {
    pub fn good_days_to_rob_bank(security: Vec<i32>, time: i32) -> Vec<i32> {
        
    }
}
```
