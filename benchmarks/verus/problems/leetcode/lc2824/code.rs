impl Solution {
    pub fn count_pairs(nums: Vec<i32>, target: i32) -> i32 {
        let mut count: i32 = 0;
        let mut i: usize = 0;
        let n: usize = nums.len();
        
        while i < n {
            let mut j: usize = i + 1;
            let mut inner_count: i32 = 0;
            
            while j < n {
                if nums[i] + nums[j] < target {
                    inner_count += 1;
                }
                j += 1;
            }
            count += inner_count;
            i += 1;
        }
        
        count
    }
}
