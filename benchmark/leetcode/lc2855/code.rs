impl Solution {
    pub fn minimum_right_shifts(nums: Vec<i32>) -> i32 {
        let n = nums.len();
        let mut break_count: usize = 0;
        let mut break_pos: usize = 0;
        let mut i: usize = 0;
        while i + 1 < n {
            if nums[i] > nums[i + 1] {
                if break_count == 0 {
                    break_pos = i;
                }
                break_count = break_count + 1;
            }
            i = i + 1;
        }
        if break_count == 0 {
            return 0;
        }
        if break_count >= 2 {
            return -1;
        }
        if nums[n - 1] <= nums[0] {
            return (n - break_pos - 1) as i32;
        }
        -1
    }
}
