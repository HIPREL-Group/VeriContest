impl Solution {
    pub fn dominant_index(nums: Vec<i32>) -> i32 {
        let n = nums.len();
        let mut max_val: i32 = nums[0];
        let mut max_idx: usize = 0;
        let mut second_max: i32 = -1;

        let mut i: usize = 1;
        while i < n {
            if nums[i] > max_val {
                second_max = max_val;
                max_val = nums[i];
                max_idx = i;
            } else if nums[i] > second_max {
                second_max = nums[i];
            }
            i += 1;
        }

        if max_val >= 2 * second_max {
            max_idx as i32
        } else {
            -1
        }
    }
}
