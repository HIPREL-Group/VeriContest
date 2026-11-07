impl Solution {
    pub fn smallest_range_i(nums: Vec<i32>, k: i32) -> i32 {
        let n = nums.len();
        let mut i: usize = 1;
        let mut min_v = nums[0];
        let mut max_v = nums[0];

        while i < n {
            let v = nums[i];
            let old_min = min_v;
            let old_max = max_v;
            min_v = if old_min < v { old_min } else { v };
            max_v = if old_max > v { old_max } else { v };
            i += 1;
        }

        let diff = max_v - min_v;
        if diff <= 2 * k {
            0
        } else {
            diff - 2 * k
        }
    }
}
