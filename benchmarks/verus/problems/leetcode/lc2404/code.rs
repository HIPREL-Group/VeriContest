impl Solution {
    pub fn most_frequent_even(nums: Vec<i32>) -> i32
    {
        let mut max_count = 0;
        let mut result: i32 = -1;
        
        for i in 0..nums.len() 
        {
            if nums[i] % 2 == 0 {
                let mut count = 0;
                
                for j in 0..nums.len() 
                {
                    if nums[j] == nums[i] {
                        count += 1;
                    }
                }

                if count > max_count || (count == max_count && nums[i] < result) {
                    max_count = count;
                    result = nums[i] as i32;
                }
            }
        }
        
        result
    }
}
