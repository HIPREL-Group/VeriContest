use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn digit(c: char) -> int {
        c as int - '0' as int
    }

    pub open spec fn rem_prefix(word: Seq<char>, m: int, n: int) -> int
        recommends
            1 <= m,
            0 <= n <= word.len(),
            forall |i: int| 0 <= i < word.len() ==> '0' <= #[trigger] word[i] <= '9',
        decreases n,
    {
        if n <= 0 {
            0
        } else {
            (Self::rem_prefix(word, m, n - 1) * 10 + Self::digit(word[n - 1])) % m
        }
    }

    pub open spec fn div_value(word: Seq<char>, m: int, i: int) -> int {
        if Self::rem_prefix(word, m, i + 1) == 0 { 1int } else { 0int }
    }

    pub fn divisibility_array(word: String, m: i32) -> (res: Vec<i32>)
        requires
            1 <= word@.len() <= 100000,
            1 <= m <= 1000000000,
            forall |i: int| 0 <= i < word@.len() ==> '0' <= #[trigger] word@[i] <= '9',
        ensures
            res.len() == word@.len(),
            forall |i: int| 0 <= i < res.len() ==> {
                &&& 0 <= #[trigger] res[i] <= 1
                &&& res[i] as int == Self::div_value(word@, m as int, i)
            },
    {
        let n = word.as_str().unicode_len();
        let mm: i64 = m as i64;
        let mut rem: i64 = 0;
        let mut i: usize = 0;
        let mut res: Vec<i32> = Vec::new();

        while i < n
            invariant
                n == word@.len(),
                1 <= n <= 100000,
                1 <= m <= 1000000000,
                mm == m as i64,
                0 <= i <= n,
                forall |k: int| 0 <= k < word@.len() ==> '0' <= #[trigger] word@[k] <= '9',
                0 <= rem < mm,
                rem as int == Self::rem_prefix(word@, m as int, i as int),
                res.len() == i,
                forall |k: int| 0 <= k < res.len() ==> {
                    &&& 0 <= #[trigger] res[k] <= 1
                    &&& res[k] as int == Self::div_value(word@, m as int, k)
                },
            decreases n - i,
        {
            let ghost old_i: int = i as int;
            let d = (word.as_str().get_char(i) as i64) - ('0' as i64);
            rem = (rem * 10 + d) % mm;
            proof {
                assert(0 <= d <= 9);
                assert(d as int == Self::digit(word@[old_i]));
                assert(rem as int == Self::rem_prefix(word@, m as int, old_i + 1));
            }
            if rem == 0 {
                res.push(1);
            } else {
                res.push(0);
            }
            proof {
                let ghost old_res = res@.drop_last();
                assert(old_res.len() == old_i);
                assert(res@ == old_res.push(res@[old_i]));
                assert(res@[old_i] as int == Self::div_value(word@, m as int, old_i));
                assert(0 <= res@[old_i] <= 1);
                assert forall |k: int| 0 <= k < res.len() implies {
                    &&& 0 <= #[trigger] res[k] <= 1
                    &&& res[k] as int == Self::div_value(word@, m as int, k)
                } by {
                    if k < old_res.len() {
                        assert(res@[k] == old_res[k]);
                    } else {
                        assert(k == old_res.len());
                    }
                }
            }
            i = i + 1;
        }

        res
    }
}

}
