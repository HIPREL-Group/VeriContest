# Earliest Time to Finish One Task

You are given a 2D integer array `tasks` where `tasks[i] = [s_i, t_i]`.

Each `[s_i, t_i]` in `tasks` represents a task with start time `s_i` that takes `t_i` units of time to finish.

Return the earliest time at which at least one task is finished.

## Example 1:

> **Input:** tasks = [[1,6],[2,3]]
> **Output:** 5
>
> **Explanation:**
>
> The first task starts at time `t = 1` and finishes at time `1 + 6 = 7`.
> The second task finishes at time `2 + 3 = 5`.
> You can finish one task at time 5.

## Example 2:

> **Input:** tasks = [[100,100],[100,100],[100,100]]
> **Output:** 200
>
> **Explanation:**
>
> All three tasks finish at time `100 + 100 = 200`.

## Constraints:

- `1 <= tasks.length <= 100`
- `tasks[i] = [s_i, t_i]`
- `1 <= s_i, t_i <= 100`

## Starter Code

```rust
impl Solution {
    pub fn earliest_time(tasks: Vec<Vec<i32>>) -> i32 {
        
    }
}
```
