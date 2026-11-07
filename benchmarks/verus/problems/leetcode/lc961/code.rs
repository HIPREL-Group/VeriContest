impl Solution {
    pub fn repeated_n_times(nums: Vec<i32>) -> i32
    {
        let n = nums.len();
        let mut i: usize = 2;

        while i < n
        {
            if nums[i] == nums[i - 1] {
                return nums[i];
            }
            if nums[i] == nums[i - 2] {
                return nums[i];
            }
            i += 1;
        }

        nums[0]
    }
}
