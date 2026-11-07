impl Solution {
    pub fn integer_replacement(mut n: i32) -> i32
    {
        let mut ans: i32 = 0;

        while n > 3
        {
            if n % 2 == 0 {
                n = n / 2;
                ans = ans + 1;
            } else {
                let t1_64: i64 = (n as i64 + 1) / 2;
                let t1 = t1_64 as i32;
                let t2 = (n - 1) / 2;

                let new_n;
                if t1 % 2 == 0 && t2 % 2 == 0 {
                    new_n = if t1 < t2 { t1 } else { t2 };
                } else if t1 % 2 == 0 {
                    new_n = t1;
                } else {
                    new_n = t2;
                }
                
                n = new_n;
                ans = ans + 2;
            }
        }

        ans + (n - 1)
    }
}
