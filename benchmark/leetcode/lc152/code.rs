impl Solution {
    pub fn max(x: i32, y: i32) -> i32
    {
        if x >= y { x } else { y }
    }

    pub fn max_product(nums: Vec<i32>) -> i32
    {
        let n = nums.len();
        let mut ans: i32 = nums[0];
        
        for i in 0..n
        {
            let mut prod: i32 = 1;
            for j in i..n
            {
                prod = prod * nums[j];
                ans = Self::max(ans, prod);
            }
        }
        
        ans
    }
}
