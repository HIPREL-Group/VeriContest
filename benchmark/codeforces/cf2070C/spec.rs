use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn count_segments(s: Seq<char>, a: Seq<i32>, p: i32, end: int) -> (int, bool)
    decreases end
{
    if end <= 0 {
        (0, false)
    } else {
        let (segs, in_b) = count_segments(s, a, p, end - 1);
        if a[end - 1] > p {
            if s[end - 1] == 'B' {
                if !in_b {
                    (segs + 1, true)
                } else {
                    (segs, true)
                }
            } else {
                (segs, false)
            }
        } else {
            (segs, in_b)
        }
    }
}

pub open spec fn valid_for_penalty(n: usize, k: i32, s: Seq<char>, a: Seq<i32>, p: i32) -> bool {
    count_segments(s, a, p, n as int).0 <= k as int
}

pub open spec fn is_optimal_penalty(n: usize, k: i32, s: Seq<char>, a: Seq<i32>, ans: i32) -> bool {
    valid_for_penalty(n, k, s, a, ans) &&
    (forall|p2: i32| 0 <= p2 && p2 < ans ==> !valid_for_penalty(n, k, s, a, p2))
}

pub struct Solution;

impl Solution {
    pub fn min_penalty(n: usize, k: i32, s: Vec<char>, a: Vec<i32>) -> (ans: i32)
        requires
            1 <= n && n <= 300000,
            0 <= k && k <= n,
            s.len() == n,
            a.len() == n,
            forall|i: int| 0 <= i && i < n ==> s@[i] == 'R' || s@[i] == 'B',
            forall|i: int| 0 <= i && i < n ==> 1 <= a@[i] && a@[i] <= 1000000000,
            valid_for_penalty(n, k, s@, a@, 1000000000), 
        ensures
            is_optimal_penalty(n, k, s@, a@, ans)
    {
    }
}

}
