impl Solution {
    pub fn return_to_boundary_count(nums: Vec<i32>) -> i32 {
        let n = nums.len();
        let mut position: i32 = 0;
        let mut count: i32 = 0;
        let mut i: usize = 0;
        while i < n {
            position += nums[i];
            if position == 0 {
                count += 1;
            }
            i += 1;
        }
        count
    }
}
