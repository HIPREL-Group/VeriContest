impl Solution {
    pub fn missing_integer(nums: Vec<i32>) -> i32
    {
        let n = nums.len();

        let mut prefix_sum = nums[0];
        let mut i: usize = 1;
        
        while i < n && nums[i] == nums[i - 1] + 1
        {
            prefix_sum += nums[i];
            i += 1;
        }

        let mut candidate = prefix_sum;
        let mut found = false;
        while !found
        {
            let mut exists = false;
            let mut j: usize = 0;
            while j < n && !exists
            {
                if nums[j] == candidate {
                    exists = true;
                }
                j += 1;
            }

            if !exists {
                found = true;
            } else {
                candidate += 1;
            }
        }

        candidate
    }
}
