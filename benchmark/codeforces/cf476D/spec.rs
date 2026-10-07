use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn max_value(n: int, k: int) -> int {
    k * (6 * n - 1)
}

pub open spec fn gcd_pos(a: int, b: int) -> int
    recommends
        a > 0 && b > 0,
    decreases a + b when a > 0 && b > 0
{
    if a == b {
        a
    } else if a > b {
        gcd_pos(a - b, b)
    } else {
        gcd_pos(a, b - a)
    }
}

pub open spec fn row_rank_k(s: Seq<i32>, kk: int) -> bool {
    &&& s.len() == 4
    &&& s[0] != s[1]
    &&& s[0] != s[2]
    &&& s[0] != s[3]
    &&& s[1] != s[2]
    &&& s[1] != s[3]
    &&& s[2] != s[3]
    &&& forall |i: int, j: int|
        0 <= i && i < j && j < 4 ==> gcd_pos(s[i] as int, s[j] as int) == kk
}

impl Solution {
    pub fn build_dreamoon_sets(n: usize, k: i32) -> (sets: Vec<Vec<i32>>)
        requires
            1 <= n <= 10000,
            1 <= k <= 100,
        ensures
            sets@.len() == n as int,
            forall |r: int| 0 <= r < n as int ==> #[trigger] row_rank_k(sets@[r]@, k as int),
            forall |r: int, c: int|
                0 <= r < n as int && 0 <= c < 4 ==>
                    1 <= (#[trigger] sets@[r]@[c] as int)
                    && (sets@[r]@[c] as int) <= max_value(n as int, k as int),
            forall |r1: int, c1: int, r2: int, c2: int|
                #![trigger sets@[r1]@[c1], sets@[r2]@[c2]]
                0 <= r1 < n as int && 0 <= c1 < 4 && 0 <= r2 < n as int && 0 <= c2 < 4
                    && (r1 != r2 || c1 != c2)
                    ==> sets@[r1]@[c1] != sets@[r2]@[c2],
    {
    }
}

}
