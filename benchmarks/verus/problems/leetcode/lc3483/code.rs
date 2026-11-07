impl Solution {
    pub fn total_numbers(digits: Vec<i32>) -> i32 {
        let mut ans: i32 = 0;
        let mut num: i32 = 100;
        while num < 1000 {
            let mut violations: i32 = 0;
            let mut d: i32 = 0;
            while d < 10 {
                let mut need: i32 = 0;
                if num / 100 == d {
                    need += 1;
                }
                if (num / 10) % 10 == d {
                    need += 1;
                }
                if num % 10 == d {
                    need += 1;
                }

                let mut have: i32 = 0;
                let mut i: usize = 0;
                while i < digits.len() {
                    if digits[i] == d {
                        have += 1;
                    }
                    i += 1;
                }

                if need > have {
                    violations += 1;
                }
                d += 1;
            }

            if violations == 0 {
                ans += 1;
            }
            num += 2;
        }
        ans
    }
}
