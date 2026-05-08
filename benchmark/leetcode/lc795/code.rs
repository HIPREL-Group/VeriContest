impl Solution {
    fn count_at_most_exec(nums: &Vec<i32>, bound: i32) -> i64 {
        let n = nums.len();
        let mut ans: i64 = 0;
        let mut cnt: i64 = 0;
        let mut i: usize = 0;
        while i < n {
            let prev_ans = ans;
            let prev_cnt = cnt;
            let value = nums[i];
            if value <= bound {
                cnt = cnt + 1;
            } else {
                cnt = 0;
            }
            ans = ans + cnt;
            i = i + 1;
        }
        ans
    }

    pub fn num_subarray_bounded_max(nums: Vec<i32>, left: i32, right: i32) -> i32 {
        let upper = Self::count_at_most_exec(&nums, right);
        let lower = Self::count_at_most_exec(&nums, left - 1);
        let result = upper - lower;
        result as i32
    }
}
