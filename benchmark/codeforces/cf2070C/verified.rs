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

proof fn lemma_monotonicity(s: Seq<char>, a: Seq<i32>, p1: i32, p2: i32, end: int)
    requires
        p1 <= p2,
        0 <= end && end <= s.len(),
    ensures
        count_segments(s, a, p1, end).0 >= count_segments(s, a, p2, end).0,
        count_segments(s, a, p1, end).0 == count_segments(s, a, p2, end).0 ==>
            (count_segments(s, a, p1, end).1 ==> count_segments(s, a, p2, end).1),
    decreases end
{
    if end > 0 {
        lemma_monotonicity(s, a, p1, p2, end - 1);
    }
}

proof fn lemma_monotonic_validity(n: usize, k: i32, s: Seq<char>, a: Seq<i32>, p1: i32, p2: i32)
    requires
        p1 <= p2,
        s.len() == n,
    ensures
        valid_for_penalty(n, k, s, a, p1) ==> valid_for_penalty(n, k, s, a, p2)
{
    lemma_monotonicity(s, a, p1, p2, n as int);
}

pub struct Solution;

impl Solution {
    pub fn check(n: usize, k: i32, s: &Vec<char>, a: &Vec<i32>, p: i32) -> (res: bool)
        requires
            1 <= n && n <= 300000,
            0 <= k && k <= n,
            s.len() == n,
            a.len() == n,
            forall|i: int| 0 <= i && i < n ==> s@[i] == 'R' || s@[i] == 'B',
            forall|i: int| 0 <= i && i < n ==> 1 <= a@[i] && a@[i] <= 1000000000,
            0 <= p && p <= 1000000000,
        ensures
            res == valid_for_penalty(n, k, s@, a@, p)
    {
        let mut segs: i32 = 0;
        let mut in_b = false;
        let mut i: usize = 0;
        while i < n
            invariant
                1 <= n && n <= 300000,
                0 <= i && i <= n,
                s.len() == n,
                a.len() == n,
                0 <= (segs as int) && (segs as int) <= (i as int),
                (segs as int) == count_segments(s@, a@, p, i as int).0,
                in_b == count_segments(s@, a@, p, i as int).1,
            decreases n - i
        {
            if a[i] > p {
                if s[i] == 'B' {
                    if !in_b {
                        segs += 1;
                        in_b = true;
                    }
                } else {
                    in_b = false;
                }
            }
            i += 1;
        }
        segs <= k
    }

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
        let mut low: i64 = 0;
        let mut high: i64 = 999999999;
        let mut ans: i32 = 1000000000;
        
        while low <= high
            invariant
                1 <= n && n <= 300000,
                0 <= k && k <= n,
                s.len() == n,
                a.len() == n,
                forall|idx: int| 0 <= idx && idx < n ==> s@[idx] == 'R' || s@[idx] == 'B',
                forall|idx: int| 0 <= idx && idx < n ==> 1 <= a@[idx] && a@[idx] <= 1000000000,
                0 <= low && low <= 1000000000,
                -1 <= high && high <= 999999999,
                ans == high as i32 + 1,
                0 <= ans && ans <= 1000000000,
                valid_for_penalty(n, k, s@, a@, ans),
                forall|p2: i32| 0 <= p2 && p2 < low ==> !valid_for_penalty(n, k, s@, a@, p2),
            decreases high - low + 1
        {
            let mid = low + (high - low) / 2;
            let low_old = low;
            if Solution::check(n, k, &s, &a, mid as i32) {
                ans = mid as i32;
                high = mid - 1;
                proof {
                    assert(valid_for_penalty(n, k, s@, a@, ans));
                }
            } else {
                low = mid + 1;
                proof {
                    assert(!valid_for_penalty(n, k, s@, a@, mid as i32));
                    assert forall|p2: i32| 0 <= p2 && p2 < low implies !valid_for_penalty(n, k, s@, a@, p2) by {
                        if p2 >= low_old {
                            if valid_for_penalty(n, k, s@, a@, p2) {
                                lemma_monotonic_validity(n, k, s@, a@, p2, mid as i32);
                                assert(valid_for_penalty(n, k, s@, a@, mid as i32)); 
                            }
                        } else {
                            assert(!valid_for_penalty(n, k, s@, a@, p2));
                        }
                    }
                }
            }
        }
        ans
    }
}
}
