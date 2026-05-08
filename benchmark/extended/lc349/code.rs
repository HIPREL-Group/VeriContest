impl Solution {
    pub fn intersection(nums1: Vec<i32>, nums2: Vec<i32>) -> Vec<i32> 
    {
        let mut result = Vec::new();
        let mut i = 0;

        while i < nums1.len()
        {
            let candidate = nums1[i];
            
            let mut j: usize = 0;
            let mut found_in_nums2: bool = false;
            
            while j < nums2.len()
            {
                if nums2[j] == candidate {
                    found_in_nums2 = true;
                }
                j = j + 1;
            }

            if found_in_nums2 {
                
                let mut k = 0;
                let mut already_in_result = false;
                
                while k < result.len()
                {
                    if result[k] == candidate {
                        already_in_result = true;
                    }
                    k = k + 1;
                }

                if !already_in_result {
                    result.push(candidate);
                }
            }
            
            i = i + 1;
        }
        
        result
    }
}
