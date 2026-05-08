pub struct NumArray {
    pub prefix: Vec<i64>,
}

impl NumArray {
    pub fn new(nums: Vec<i32>) -> Self
    {
        let n = nums.len();
        let mut prefix: Vec<i64> = Vec::new();
        prefix.push(0i64);
        let mut i: usize = 0;
        while i < n
        {
            let next = prefix[i] + nums[i] as i64;
            prefix.push(next);
            i += 1;
        }
        NumArray { prefix }
    }

    pub fn sum_range(&self, left: i32, right: i32) -> i32
    {
        let r = right as usize;
        let l = left as usize;
        (self.prefix[r + 1] - self.prefix[l]) as i32
    }
}
