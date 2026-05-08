impl Solution {
    pub fn rob(nums: Vec<i32>) -> i32 {
        let n = nums.len();
        if n == 1 {
            return nums[0];
        }
        let mut a = nums[0];
        let mut b = if nums[0] > nums[1] { nums[0] } else { nums[1] };
        let mut i: usize = 2;
        while i < n {
            let c = if a + nums[i] > b { a + nums[i] } else { b };
            a = b;
            b = c;
            i = i + 1;
        }
        b
    }
}
