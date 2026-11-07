impl Solution {
    pub fn abs(x: i32) -> i32
    {
        if x < 0 { -x } else { x }
    }

    pub fn max(x: i32, y: i32) -> i32
    {
        if x >= y { x } else { y }
    }

    pub fn min(x: i32, y: i32) -> i32
    {
        if x <= y { x } else { y }
    }

    pub fn maximum_strong_pair_xor(nums: Vec<i32>) -> i32
    {
        let mut max_xor = 0;
        for i in 0..nums.len() 
        {
            for j in i..nums.len() 
            {
                if Self::abs(nums[i] - nums[j]) <= Self::min(nums[i], nums[j]) {
                    let current_xor = nums[i] ^ nums[j];
                    max_xor = Self::max(max_xor, current_xor);
                }
            }
        }
        
        max_xor
    }
}
