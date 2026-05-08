impl Solution {
    pub fn min_operations(nums: Vec<i32>, k: i32) -> i32 
    {
        let mut count: i32 = 0;
        for i in 0..nums.len() 
        {
            if nums[i] < k {
                count += 1;
            }
        }
        return count;
    }
}
