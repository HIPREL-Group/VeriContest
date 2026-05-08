impl Solution {
    pub fn product_except_self(nums: Vec<i32>) -> Vec<i32>
    {
        let n = nums.len();
        
        let mut pre = Vec::with_capacity(n);
        for i in 0..n 
        {
            pre.push(nums[i]);
        }
        
        let mut suf = Vec::with_capacity(n);
        for i in 0..n 
        {
            suf.push(nums[i]);
        }

        for i in 1..n 
        {
            pre[i] = pre[i] * pre[i - 1];
            suf[n - 1 - i] = suf[n - 1 - i] * suf[n - i];
        }

        pre.insert(0, 1);
        suf.push(1);

        let mut res = Vec::with_capacity(n);
        for i in 0..n 
        {
            res.push(pre[i] * suf[i + 1]);
        }
        res
    }
}
