impl Solution {
    pub fn find_closest_number(nums: Vec<i32>) -> i32 {
        let n = nums.len();
        let mut best = nums[0];
        let mut i: usize = 1;

        while i < n {
            let current = nums[i];
            let prev_best = best;
            let prev_best_abs = if prev_best < 0 { -prev_best } else { prev_best };
            let current_abs = if current < 0 { -current } else { current };
            let new_best = if current_abs < prev_best_abs || (current_abs == prev_best_abs && current > prev_best) {
                current
            } else {
                prev_best
            };

            best = new_best;
            i += 1;
        }

        best
    }
}
