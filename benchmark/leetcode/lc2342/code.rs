impl Solution {
    fn digit_sum(mut x: i32) -> i64 {
        let mut s: i64 = 0;
        while x > 0 {
            s = s + (x % 10) as i64;
            x = x / 10;
        }
        s
    }

    pub fn maximum_sum(nums: Vec<i32>) -> i32 {
        let mut ans: i32 = -1;
        let n = nums.len();
        let mut i: usize = 0;
        let mut found: bool = false;
        let mut bi: usize = 0;
        let mut bj: usize = 0;

        while i < n {
            let mut j: usize = i + 1;
            while j < n {
                let si = Self::digit_sum(nums[i]);
                let sj = Self::digit_sum(nums[j]);
                if si == sj {
                    let cur = nums[i] + nums[j];
                    if !found || cur > ans {
                        found = true;
                        bi = i;
                        bj = j;
                        ans = cur;
                    }
                }
                j = j + 1;
            }
            i = i + 1;
        }

        ans
    }
}
