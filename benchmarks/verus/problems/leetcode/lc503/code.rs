impl Solution {
    pub fn next_greater_elements(nums: Vec<i32>) -> Vec<i32>
    {
        let n = nums.len();

        let mut res: Vec<i32> = Vec::new();
        let mut idx: usize = 0;
        while idx < n
        {
            res.push(-1);
            idx = idx + 1;
        }
        let mut i: usize = 0;
        while i < n
        {
            let mut k: usize = 1;
            while k < n
            {
                let j = if i + k < n { i + k } else { i + k - n };
                if nums[j] > nums[i] {
                    res[i] = nums[j];
                    k = n;
                } else {
                    k = k + 1;
                }
            }
            i = i + 1;
        }
        res
    }
}
