impl Solution {
    pub fn majority_element(nums: Vec<i32>) -> i32
    {
        let n = nums.len();
        let threshold = n / 2;
        let mut found = false;
        let mut candidate = nums[0];
        
        let mut i = 0;
        while i < nums.len() && !found
        {
            let mut count = 0;
            candidate = nums[i];

            for j in 0..n 
            {
                if nums[j] == candidate {
                    count += 1;
                }
            }
            
            if count > threshold {
                found = true;
            }

            i += 1;
        }
        
        candidate
    }
}
