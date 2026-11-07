use std::collections::HashSet;

impl Solution {
    pub fn contains_duplicate(nums: Vec<i32>) -> bool
    {
        let mut seen = HashSet::new();
        for i in 0..nums.len() 
        {
            if seen.contains(&nums[i]) {
                return true;
            }
            seen.insert(nums[i]);
        }
        false
    }
}
