impl Solution {
    pub fn is_monotonic(nums: Vec<i32>) -> bool {
        let n = nums.len();
        let mut inc_bad: i32 = 0;
        let mut dec_bad: i32 = 0;
        let mut i: usize = 0;

        while i + 1 < n {
            if nums[i] > nums[i + 1] {
                inc_bad = inc_bad + 1;
            }
            if nums[i] < nums[i + 1] {
                dec_bad = dec_bad + 1;
            }
            i = i + 1;
        }

        inc_bad == 0 || dec_bad == 0
    }
}
