impl Solution {
    fn sub_one(n: i32) -> i32 {
        let m = n / 2;
        if m % 2 == 0 {
            1
        } else {
            let t = Self::sub_one(m);
            2 * t
        }
    }

    fn min_one(n: i32) -> i32 {
        if n % 2 == 0 {
            -1
        } else {
            let s = Self::sub_one(n);
            n - s
        }
    }

    pub fn min_bitwise_array(nums: Vec<i32>) -> Vec<i32> {
        let mut ans = Vec::new();
        let mut i: usize = 0;
        while i < nums.len() {
            let a = Self::min_one(nums[i]);
            ans.push(a);
            i += 1;
        }
        ans
    }
}
