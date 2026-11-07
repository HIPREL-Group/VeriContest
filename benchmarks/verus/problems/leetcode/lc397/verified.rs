use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn steps_to_one(n: int) -> int
        decreases n, 
    {
        if n <= 3 {
            if n <= 1 { 0 } else { n - 1 }
        } else if n % 2 == 0 {
            1 + Self::steps_to_one(n / 2)
        } else {
            let t1 = (n + 1) / 2;
            let t2 = (n - 1) / 2;
            
            if t1 % 2 == 0 && t2 % 2 == 0 {
                2 + Self::steps_to_one(if t1 <= t2 { t1 } else { t2 })
            } else if t1 % 2 == 0 {
                2 + Self::steps_to_one(t1)
            } else {
                2 + Self::steps_to_one(t2)
            }
        }
    }

    proof fn steps_non_negative(n: int)
        requires 
            n >= 1,
        ensures 
            Self::steps_to_one(n) >= 0,
        decreases n, 
    {
        if n <= 3 {
        } else if n % 2 == 0 {
            Self::steps_non_negative(n / 2);
        } else {
            let t1 = (n + 1) / 2;
            let t2 = (n - 1) / 2;
            
            if t1 % 2 == 0 && t2 % 2 == 0 {
                let chosen = if t1 <= t2 { t1 } else { t2 };
                Self::steps_non_negative(chosen);
            } else if t1 % 2 == 0 {
                Self::steps_non_negative(t1);
            } else {
                Self::steps_non_negative(t2);
            }
        }
    }

    pub fn integer_replacement(mut n: i32) -> (res: i32)
        requires
            1 <= n <= i32::MAX,
            0 <= Self::steps_to_one(n as int) < i32::MAX - 2, 
        ensures
            res == Self::steps_to_one(n as int),
    {
        let mut ans: i32 = 0;
        let ghost original_n = n as int;

        while n > 3
            invariant
                1 <= n <= i32::MAX,
                0 <= Self::steps_to_one(original_n) < i32::MAX - 2,
                0 <= ans < i32::MAX - 2,
                0 <= Self::steps_to_one(n as int) < i32::MAX - 2,
                ans + Self::steps_to_one(n as int) == Self::steps_to_one(original_n),
            decreases n, 
        {
            if n % 2 == 0 {
                proof {
                    Self::steps_non_negative((n / 2) as int);
                }
                n = n / 2;
                ans = ans + 1;
            } else {
                let t1_64: i64 = (n as i64 + 1) / 2;
                let t1 = t1_64 as i32;
                let t2 = (n - 1) / 2;

                let new_n;
                if t1 % 2 == 0 && t2 % 2 == 0 {
                    new_n = if t1 < t2 { t1 } else { t2 };
                    proof {
                        Self::steps_non_negative(new_n as int);
                    }
                } else if t1 % 2 == 0 {
                    new_n = t1;
                    proof {
                        Self::steps_non_negative(new_n as int);
                    }
                } else {
                    new_n = t2;
                    proof {
                        Self::steps_non_negative(new_n as int);
                    }
                }
                
                n = new_n;
                ans = ans + 2;
            }
        }

        ans + (n - 1)
    }
}

}