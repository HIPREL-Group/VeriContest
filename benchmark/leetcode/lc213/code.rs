impl Solution {
    pub fn rob(nums: Vec<i32>) -> i32 {
        let n = nums.len();
        if n == 1 {
            return nums[0];
        }
        let hi1: usize = n - 2;
        let rob1: i32;
        if hi1 == 0 {
            rob1 = nums[0];
        } else {
            let mut a: i32 = nums[0];
            let mut b: i32 = if nums[0] > nums[1] { nums[0] } else { nums[1] };
            let mut i: usize = 2;
            while i <= hi1 {
                let c = if a + nums[i] > b { a + nums[i] } else { b };
                a = b;
                b = c;
                i = i + 1;
            }
            rob1 = b;
        }
        let hi2: usize = n - 1;
        let rob2: i32;
        if n == 2 {
            rob2 = nums[1];
        } else {
            let mut a: i32 = nums[1];
            let mut b: i32 = if nums[1] > nums[2] { nums[1] } else { nums[2] };
            let mut i: usize = 3;
            while i <= hi2 {
                let c = if a + nums[i] > b { a + nums[i] } else { b };
                a = b;
                b = c;
                i = i + 1;
            }
            rob2 = b;
        }
        if rob1 > rob2 { rob1 } else { rob2 }
    }
}
