impl Solution {
    pub fn minimum_cost(nums: Vec<i32>) -> i32 {
        let n = nums.len();
        let mut min1: i32 = 51;
        let mut min2: i32 = 51;
        let mut i: usize = 1;
        while i < n {
            if nums[i] < min1 {
                min2 = min1;
                min1 = nums[i];
            } else if nums[i] < min2 {
                min2 = nums[i];
            }
            i = i + 1;
        }
        nums[0] + min1 + min2
    }
}
