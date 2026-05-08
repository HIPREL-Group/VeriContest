impl Solution {
    pub fn move_zeroes(nums: &mut Vec<i32>)
    {
        let mut left = 0;
        let n = nums.len();

        for right in 0..n
        {
            if nums[right] != 0 {
                let temp = nums[left];
                nums[left] = nums[right];
                nums[right] = temp;
                left += 1;
            }
        }
    }
}
