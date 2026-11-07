impl Solution {
    pub fn sort_even_odd(nums: Vec<i32>) -> Vec<i32>
    {
        let mut nums = nums;
        let n = nums.len();
        let mut i: usize = 2;
        while i < n
        {
            let mut j: usize = i;
            while j != 0 && nums[j - 2] > nums[j]
            {
                let tmp_left = nums[j - 2];
                let tmp_right = nums[j];
                nums[j - 2] = tmp_right;
                nums[j] = tmp_left;
                j = j - 2;
            }
            i = i + 2;
        }
        let mut i: usize = 3;
        while i < n
        {
            let mut j: usize = i;
            while j > 1 && nums[j - 2] < nums[j]
            {
                let tmp_left = nums[j - 2];
                let tmp_right = nums[j];
                nums[j - 2] = tmp_right;
                nums[j] = tmp_left;
                j = j - 2;
            }
            i = i + 2;
        }
        nums
    }
}
