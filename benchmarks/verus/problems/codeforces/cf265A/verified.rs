use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn final_position(s: Seq<u8>, t: Seq<u8>, k: int) -> int
    recommends
        0 <= k <= t.len(),
        s.len() >= 1,
    decreases k,
{
    if k <= 0 {
        0int
    } else {
        let prev = final_position(s, t, k - 1);
        if 0 <= prev && prev < s.len() && s[prev] == t[k - 1] {
            prev + 1
        } else {
            prev
        }
    }
}

proof fn lemma_final_position_bounds(s: Seq<u8>, t: Seq<u8>, k: int)
    requires
        0 <= k <= t.len(),
    ensures
        0 <= final_position(s, t, k) <= k,
    decreases k,
{
    if k <= 0 {
    } else {
        lemma_final_position_bounds(s, t, k - 1);
    }
}

impl Solution {
    pub fn final_pos(s: Vec<u8>, t: Vec<u8>) -> (result: usize)
        requires
            1 <= s.len() <= 50,
            1 <= t.len() <= 50,
            forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] <= 2u8,
            forall|i: int| 0 <= i < t.len() ==> #[trigger] t[i] <= 2u8,
            final_position(s@, t@, t.len() as int) < s.len(),
        ensures
            result as int == final_position(s@, t@, t.len() as int) + 1,
    {
        let mut pos: usize = 0;
        let m = t.len();
        let n = s.len();
        let mut i: usize = 0;
        while i < m
            invariant
                0 <= i <= m,
                m == t.len(),
                n == s.len(),
                1 <= n <= 50,
                1 <= m <= 50,
                pos as int == final_position(s@, t@, i as int),
                pos <= i,
            decreases m - i,
        {
            proof {
                lemma_final_position_bounds(s@, t@, i as int + 1);
            }
            if pos < n && s[pos] == t[i] {
                pos = pos + 1;
            }
            i = i + 1;
        }
        pos + 1
    }
}

}
