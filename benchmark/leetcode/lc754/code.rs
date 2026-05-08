impl Solution {
    pub fn reach_number(target: i32) -> i32 {
        let target_abs = if target < 0 { -target } else { target };
        let mut step: i32 = 0;
        let mut sum: i32 = 0;
        while sum < target_abs {
            step += 1;
            sum += step;
        }
        if (sum - target_abs) % 2 != 0 {
            step += 1;
            sum += step;
            if (sum - target_abs) % 2 != 0 {
                step += 1;
                sum += step;
            }
        }
        step
    }
}
