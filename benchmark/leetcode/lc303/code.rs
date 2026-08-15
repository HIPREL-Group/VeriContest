pub struct NumArray {
    pub nums: Vec<i32>,
}

impl NumArray {
    pub fn new(nums: Vec<i32>) -> Self
    {
        NumArray { nums }
    }

    pub fn sum_range(&self, left: i32, right: i32) -> i32
    {
        let mut sum: i64 = 0;
        let mut i: usize = left as usize;
        while i <= right as usize
        {
            sum = sum + self.nums[i] as i64;
            i += 1;
        }
        sum as i32
    }
}
