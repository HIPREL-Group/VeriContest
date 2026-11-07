# Earliest Finish Time for Land and Water Rides I

You are given two categories of theme park attractions: land rides and water rides.

- `landStartTime[i]` is the earliest time the `i`-th land ride can be boarded.
- `landDuration[i]` is how long the `i`-th land ride lasts.
- `waterStartTime[j]` is the earliest time the `j`-th water ride can be boarded.
- `waterDuration[j]` is how long the `j`-th water ride lasts.

A tourist must experience exactly one ride from each category, in either order.

- A ride may be started at its opening time or any later moment.
- If a ride is started at time `t`, it finishes at time `t + duration`.
- Immediately after finishing one ride, the tourist may board the other (if it is already open) or wait until it opens.

Return the earliest possible time at which the tourist can finish both rides.

## Example 1:

> **Input:** landStartTime = [2,8], landDuration = [4,1], waterStartTime = [6], waterDuration = [3]
> **Output:** 9
>
> **Explanation:**
> Plan A (land ride 0 -> water ride 0):
> - Start land ride 0 at time 2. Finish at 6.
> - Water ride 0 opens at time 6. Start immediately at 6, finish at 9.
>
> Other valid plans finish at times 10, 12, and 13, so 9 is earliest.

## Example 2:

> **Input:** landStartTime = [5], landDuration = [3], waterStartTime = [1], waterDuration = [10]
> **Output:** 14
>
> **Explanation:**
> - Water then land: finish at 14.
> - Land then water: finish at 18.
>
> The earliest finish time is 14.

## Constraints:

- `1 <= n, m <= 100`
- `landStartTime.length == landDuration.length == n`
- `waterStartTime.length == waterDuration.length == m`
- `1 <= landStartTime[i], landDuration[i], waterStartTime[j], waterDuration[j] <= 1000`

## Starter Code

```rust
impl Solution {
    pub fn earliest_finish_time(land_start_time: Vec<i32>, land_duration: Vec<i32>, water_start_time: Vec<i32>, water_duration: Vec<i32>) -> i32 {
        
    }
}
```
