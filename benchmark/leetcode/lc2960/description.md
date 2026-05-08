# Count Tested Devices After Test Operations

You are given a 0-indexed integer array `batteryPercentages` having length `n`, denoting the battery percentages of `n` 0-indexed devices.

Your task is to test each device `i` in order from `0` to `n - 1`, by performing the following test operations:

- If `batteryPercentages[i]` is **greater** than `0`:
  - **Increment** the count of tested devices.
  - **Decrease** the battery percentage of all devices with indices `j` in the range `[i + 1, n - 1]` by `1`, ensuring their battery percentage **never goes below** `0`, i.e, `batteryPercentages[j] = max(0, batteryPercentages[j] - 1)`.
  - Move to the next device.
- Otherwise, move to the next device without performing any test.

Return an integer denoting the number of devices that will be tested after performing the test operations in order.

## Examples

**Example 1:**
Input: batteryPercentages = [1,1,2,1,3]
Output: 3

**Example 2:**
Input: batteryPercentages = [0,1,2]
Output: 2

## Constraints

- 1 <= n == batteryPercentages.length <= 100
- 0 <= batteryPercentages[i] <= 100

## Starter Code

```rust
impl Solution {
    pub fn count_tested_devices(battery_percentages: Vec<i32>) -> i32 {
        
    }
}
```
