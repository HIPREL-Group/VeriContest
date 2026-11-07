use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn pref_sum(a: Seq<i64>, idx: int) -> int
    recommends
        0 <= idx <= a.len(),
    decreases idx,
{
    if idx <= 0 {
        0int
    } else {
        pref_sum(a, idx - 1) + a[idx - 1] as int
    }
}

pub open spec fn leftmost_l(s: Seq<u8>, lo: int, hi: int) -> int
    recommends
        0 <= lo <= hi <= s.len(),
    decreases if hi > lo { hi - lo } else { 0int },
{
    if lo >= hi {
        -1int
    } else if s[lo] == 1u8 {
        lo
    } else {
        leftmost_l(s, lo + 1, hi)
    }
}

pub open spec fn rightmost_r(s: Seq<u8>, lo: int, hi: int) -> int
    recommends
        0 <= lo <= hi <= s.len(),
    decreases if hi > lo { hi - lo } else { 0int },
{
    if lo >= hi {
        -1int
    } else if s[hi - 1] == 2u8 {
        hi - 1
    } else {
        rightmost_r(s, lo, hi - 1)
    }
}



pub open spec fn greedy(a: Seq<i64>, s: Seq<u8>, lo: int, hi: int) -> int
    recommends
        a.len() == s.len(),
        0 <= lo <= hi <= a.len(),
    decreases if hi > lo { hi - lo } else { 0int },
{
    let l = leftmost_l(s, lo, hi);
    let r = rightmost_r(s, lo, hi);
    if l < 0 || r < 0 || l >= r {
        0int
    } else {
        (pref_sum(a, r + 1) - pref_sum(a, l)) + greedy(a, s, l + 1, r)
    }
}


impl Solution {
    pub fn max_score(a: Vec<i64>, s: Vec<u8>) -> (result: i64)
        requires
            2 <= a.len() <= 200_000,
            a.len() == s.len(),
            forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= 100_000,
            forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] == 1u8 || s[i] == 2u8,
        ensures
            result as int == greedy(a@, s@, 0, a.len() as int),
    {
    }
}

}
