impl Solution {
    pub fn missing_number(nums: Vec<i32>) -> i32
    {
        let n = nums.len() as i32;
        let mut candidate = 0;
        let mut found_missing = false;
        
        while candidate <= n && !found_missing
        {
            let mut exists_in_nums = false;
            let mut ix = 0;
            
            while ix < nums.len() && !exists_in_nums
            {
                if nums[ix] == candidate {
                    exists_in_nums = true;
                }
                ix += 1;
            }
            
            if !exists_in_nums {
                found_missing = true;
            } else {
                candidate += 1;
            }
        }

        candidate
    }
}
