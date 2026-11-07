impl Solution {
    pub fn missing_rolls(rolls: Vec<i32>, mean: i32, n: i32) -> Vec<i32> {
        let mut observed_sum = 0i128;
        let mut i: usize = 0;
        while i < rolls.len() {
            observed_sum += rolls[i] as i128;
            i += 1;
        }

        let missing_sum = mean as i128 * (rolls.len() as i128 + n as i128) - observed_sum;
        if missing_sum < n as i128 || missing_sum > 6 * n as i128 {
            return Vec::new();
        }

        let mut result: Vec<i32> = Vec::new();
        let mut remaining_sum = missing_sum;
        let mut remaining_slots = n as i128;
        while remaining_slots > 0 {
            let candidate = remaining_sum - 6 * (remaining_slots - 1);
            let val = if candidate > 1 { candidate } else { 1 };
            result.push(val as i32);
            remaining_sum -= val;
            remaining_slots -= 1;
        }

        result
    }
}
