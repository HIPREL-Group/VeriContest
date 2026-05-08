use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn seq_sum(s: Seq<int>) -> int
        decreases s.len(),
    {
        if s.len() == 0 {
            0
        } else {
            s[0] + Self::seq_sum(s.subrange(1, s.len() as int))
        }
    }

    pub open spec fn seq_product(s: Seq<int>) -> int
        decreases s.len(),
    {
        if s.len() == 0 {
            1
        } else {
            s[0] * Self::seq_product(s.subrange(1, s.len() as int))
        }
    }

    pub open spec fn is_valid_partition(s: Seq<int>, n: int) -> bool {
        s.len() >= 2
        && (forall |i: int| 0 <= i < s.len() ==> #[trigger] s[i] >= 1)
        && Self::seq_sum(s) == n
    }

    pub fn integer_break(n: i32) -> (result: i32)
        requires
            2 <= n <= 58,
        ensures
            result >= 1,
            exists |s: Seq<int>|
                #[trigger] Self::is_valid_partition(s, n as int)
                && Self::seq_product(s) == result as int,
            forall |s: Seq<int>|
                #[trigger] Self::is_valid_partition(s, n as int)
                ==> Self::seq_product(s) <= result as int,
    {
        if n == 2 {
            return 1;
        }
        if n == 3 {
            return 2;
        }
        let q = n / 3;
        let r = n % 3;
        let mut p: i32 = 1;
        let mut i: i32 = 0;

        if r == 0 {
            while i < q
            {
                p = p * 3;
                i += 1;
            }
            p
        } else if r == 1 {
            while i < q - 1
            {
                p = p * 3;
                i += 1;
            }
            p * 4
        } else {
            while i < q
            {
                p = p * 3;
                i += 1;
            }
            p * 2
        }
    }
}

}
