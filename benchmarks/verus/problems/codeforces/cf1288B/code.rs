impl Solution {
    pub fn meme_pair_count(a_max: i64, b_max: i64) -> i64 {
        let mut ans: i64 = 0;
        if 9 <= b_max {
            ans = ans + a_max;
        }
        if 99 <= b_max {
            ans = ans + a_max;
        }
        if 999 <= b_max {
            ans = ans + a_max;
        }
        if 9_999 <= b_max {
            ans = ans + a_max;
        }
        if 99_999 <= b_max {
            ans = ans + a_max;
        }
        if 999_999 <= b_max {
            ans = ans + a_max;
        }
        if 9_999_999 <= b_max {
            ans = ans + a_max;
        }
        if 99_999_999 <= b_max {
            ans = ans + a_max;
        }
        if 999_999_999 <= b_max {
            ans = ans + a_max;
        }
        ans
    }
}
