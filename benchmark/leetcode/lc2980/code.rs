impl Solution {
    pub fn has_trailing_zeros(nums: Vec<i32>) -> bool
    {
        let n = nums.len();
        let mut first_even: usize = n;
        let mut i: usize = 0;
        while i < n {
            if nums[i] % 2 == 0 {
                if first_even != n {
                    return true;
                }
                first_even = i;
            }
            i = i + 1;
        }
        false
    }
}
