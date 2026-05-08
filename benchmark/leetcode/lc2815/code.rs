impl Solution {
    fn max_digit(num: i32) -> i32 {
        if num < 10 {
            num
        } else {
            let rest = Self::max_digit(num / 10);
            let d = num % 10;
            if d > rest { d } else { rest }
        }
    }

    pub fn max_sum(nums: Vec<i32>) -> i32 {
        let mut ans: i32 = -1;
        let mut i: usize = 0;
        while i < nums.len() {
            let mut cur: i32 = -1;
            let mut j: usize = i + 1;
            while j < nums.len() {
                let di = Self::max_digit(nums[i]);
                let dj = Self::max_digit(nums[j]);
                if di == dj {
                    let s = nums[i] + nums[j];
                    if s > cur {
                        cur = s;
                    }
                }
                j = j + 1;
            }
            if cur > ans {
                ans = cur;
            }
            i = i + 1;
        }
        ans
    }
}
