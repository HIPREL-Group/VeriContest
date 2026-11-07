impl Solution {
    pub fn min_cost(nums: Vec<i32>, cost: Vec<i32>) -> i64 {
        let max_value: usize = 1_000_000;
        let n = nums.len();
        let mut weights: Vec<i64> = Vec::new();
        let mut zeroes: usize = 0;

        while zeroes < max_value + 1 {
            weights.push(0);
            zeroes = zeroes + 1;
        }

        let mut total_weight: i64 = 0;
        let mut current: i64 = 0;
        let mut i: usize = 0;
        while i < n {
            let value = nums[i] as usize;
            let c = cost[i] as i64;
            weights[value] = weights[value] + c;
            total_weight = total_weight + c;
            current = current + (nums[i] as i64 - 1) * c;
            i = i + 1;
        }

        let mut target: usize = 1;
        let mut prefix: i64 = weights[1];
        let mut best: i64 = current;
        while target < max_value {
            let delta = prefix - (total_weight - prefix);
            current = current + delta;
            target = target + 1;
            prefix = prefix + weights[target];
            if current < best {
                best = current;
            }
        }

        best
    }
}
