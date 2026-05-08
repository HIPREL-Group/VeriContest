impl Solution {
    pub fn max_value_after_reverse(nums: Vec<i32>) -> i32 {
        let n = nums.len();
        let mut total: i64 = 0;
        let mut gain: i64 = 0;
        let mut min_of_max: i64 = 200001;
        let mut max_of_min: i64 = -200001;
        let mut i: usize = 0;
        while i < n - 1 {
            let a = nums[i] as i64;
            let b = nums[i + 1] as i64;
            let diff: i64 = if a >= b { a - b } else { b - a };
            total = total + diff;
            let first = nums[0] as i64;
            let last = nums[n - 1] as i64;
            let g1: i64 = (if first >= b { first - b } else { b - first }) - diff;
            let g2: i64 = (if last >= a { last - a } else { a - last }) - diff;
            if g1 > gain {
                gain = g1;
            }
            if g2 > gain {
                gain = g2;
            }
            let pair_max: i64 = if a >= b { a } else { b };
            let pair_min: i64 = if a <= b { a } else { b };
            if pair_max < min_of_max {
                min_of_max = pair_max;
            }
            if pair_min > max_of_min {
                max_of_min = pair_min;
            }
            i = i + 1;
        }
        let interior: i64 = if max_of_min > min_of_max {
            2 * (max_of_min - min_of_max)
        } else {
            0
        };
        if interior > gain {
            gain = interior;
        }
        (total + gain) as i32
    }
}
