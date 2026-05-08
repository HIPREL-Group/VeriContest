impl Solution {
    pub fn majority_element(nums: Vec<i32>) -> Vec<i32>
    {
        let n = nums.len();
        let threshold = n / 3;
        let mut results = Vec::new();
        
        let mut i = 0;
        while i < nums.len() 
        {
            let mut count = 0;
            let candidate = nums[i];

            for j in 0..n 
            {
                if nums[j] == candidate {
                    count += 1;
                }
            }

            if count > threshold {
                let mut found = false;
                for j in 0..results.len()
                {
                    if results[j] == candidate {
                        found = true;
                    }
                }
                if !found {
                    results.push(candidate);
                }
            }

            i += 1;
        }

        results
    }
}
