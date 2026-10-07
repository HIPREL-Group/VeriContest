impl Solution {
    pub fn find_non_min_or_max(nums: Vec<i32>) -> i32 
    {
        if nums.len() < 3 {
            return -1;
        }

        let mut min_val = nums[0];
        let mut max_val = nums[0];

        let mut i = 1;
        while i < nums.len()
        {
            if nums[i] < min_val {
                min_val = nums[i];
            }
            if nums[i] > max_val {
                max_val = nums[i];
            }
            i += 1;
        }
        
        let mut j = 0;
        while j < nums.len()
        {
            if nums[j] != min_val && nums[j] != max_val {
                return nums[j];
            }
            j += 1;
        }

        -1
    }
}
