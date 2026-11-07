impl Solution {
    pub fn search_insert(nums: Vec<i32>, target: i32) -> i32 
    {
        let mut start = 0;
        let mut end = nums.len() as i32 - 1;
        
        while start <= end 
        {
            
            let mid = (start + end) / 2;
            let mid_val = nums[mid as usize];
            
            if mid_val == target {
                return mid;
            } else if mid_val > target {
                end = mid - 1;
            } else {
                start = mid + 1;
            }
        }
        
        start
    }
}
