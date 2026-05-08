impl Solution {
    pub fn max_sub_array(nums: Vec<i32>) -> i32
    {
        let n = nums.len();

        let mut max_here: i64 = nums[0] as i64;
        let mut max_so_far: i64 = nums[0] as i64;

        let mut i: usize = 1;

        while i < n
        {
            let old_max_here: i64 = max_here;
            let candidate: i64 = old_max_here + nums[i] as i64;
            let old_max_so_far: i64 = max_so_far;

            if candidate >= nums[i] as i64 {
                max_here = candidate;
            } else {
                max_here = nums[i] as i64;
            }
            if max_here > max_so_far {
                max_so_far = max_here;
            }

            i += 1;
        }

        max_so_far as i32
    }
}
