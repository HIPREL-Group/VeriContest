impl Solution {
    pub fn is_good_array(nums: Vec<i32>) -> bool
    {
        let mut g = nums[0];
        let mut i: usize = 1;
        while i < nums.len()
        {
            let mut a = g;
            let mut b = nums[i];
            while b != 0
            {
                let temp = a % b;
                a = b;
                b = temp;
            }
            g = a;
            i = i + 1;
        }
        g == 1
    }
}
