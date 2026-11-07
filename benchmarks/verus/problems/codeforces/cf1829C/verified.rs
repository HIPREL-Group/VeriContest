use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn valid_mask(x: i32) -> bool {
    0 <= x <= 3
}

pub open spec fn feasible_cost(m: Seq<i32>, s: Seq<i32>, v: int) -> bool {
    (exists|i: int| 0 <= i < m.len() && s[i] == 3 && v == m[i] as int)
        || (exists|i: int, j: int| 0 <= i < m.len() && 0 <= j < m.len() && s[i] == 2 && s[j] == 1
            && v == m[i] as int + m[j] as int)
}

pub struct Solution;

impl Solution {
    fn min_for_mask(m: &Vec<i32>, s: &Vec<i32>, target: i32) -> (res: (i32, bool))
        requires
            m.len() == s.len(),
            1 <= m.len() <= 200_000,
            target == 1 || target == 2 || target == 3,
            forall|i: int| 0 <= i < m.len() ==> 1 <= #[trigger] m[i] <= 200_000,
            forall|i: int| 0 <= i < s.len() ==> valid_mask(#[trigger] s[i]),
        ensures
            res.1 <==> exists|i: int| 0 <= i < m.len() && s[i] == target,
            !res.1 ==> res.0 == 1_000_000_000,
            res.1 ==> exists|i: int| 0 <= i < m.len() && s[i] == target && res.0 == m[i],
            forall|i: int| 0 <= i < m.len() && s[i] == target ==> res.0 <= m[i],
    {
        let inf: i32 = 1_000_000_000;
        let n = m.len();
        let mut best = inf;
        let mut seen = false;

        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                n == m.len(),
                n == s.len(),
                1 <= n <= 200_000,
                target == 1 || target == 2 || target == 3,
                forall|k: int| 0 <= k < n ==> 1 <= #[trigger] m[k] <= 200_000,
                forall|k: int| 0 <= k < n ==> valid_mask(#[trigger] s[k]),
                seen <==> exists|k: int| 0 <= k < i as int && s[k] == target,
                !seen ==> best == inf,
                seen ==> exists|k: int| 0 <= k < i as int && s[k] == target && best == m[k],
                forall|k: int| 0 <= k < i as int && s[k] == target ==> best <= m[k],
            decreases n - i,
        {
            if s[i] == target {
                if !seen {
                    seen = true;
                    best = m[i];
                } else if m[i] < best {
                    best = m[i];
                }
            }
            i = i + 1;
        }

        (best, seen)
    }

    pub fn min_minutes(m: Vec<i32>, s: Vec<i32>) -> (result: i32)
        requires
            1 <= m.len() <= 200_000,
            m.len() == s.len(),
            forall|i: int| 0 <= i < m.len() ==> 1 <= #[trigger] m[i] <= 200_000,
            forall|i: int| 0 <= i < s.len() ==> valid_mask(#[trigger] s[i]),
        ensures
            result == -1 ==> !exists|v: int| feasible_cost(m@, s@, v),
            result != -1 ==> feasible_cost(m@, s@, result as int),
            result != -1 ==> forall|v: int| feasible_cost(m@, s@, v) ==> result as int <= v,
    {
        let inf: i32 = 1_000_000_000;
        let n = m.len();

        let r11 = Solution::min_for_mask(&m, &s, 3);
        let r10 = Solution::min_for_mask(&m, &s, 2);
        let r01 = Solution::min_for_mask(&m, &s, 1);

        let best11 = r11.0;
        let seen11 = r11.1;
        let best10 = r10.0;
        let seen10 = r10.1;
        let best01 = r01.0;
        let seen01 = r01.1;

        let cand11 = if seen11 { best11 } else { inf };
        let candpair = if best10 < inf && best01 < inf {
            best10 + best01
        } else {
            inf
        };
        let ans = if cand11 < candpair { cand11 } else { candpair };

        if ans >= inf {
            proof {
                assert(cand11 == inf);
                assert(candpair == inf);
                assert(!seen11);
                assert(!seen10 || !seen01);
                assert(!exists|v: int| feasible_cost(m@, s@, v)) by {
                    assert forall|v: int| feasible_cost(m@, s@, v) implies false by {
                        if exists|k: int| 0 <= k < n as int && s[k] == 3 && v == m[k] as int {
                            let k = choose|k: int| 0 <= k < n as int && s[k] == 3 && v == m[k] as int;
                            assert(0 <= k < n as int);
                            assert(s[k] == 3);
                            assert(seen11);
                        } else {
                            let i0 = choose|i0: int, j0: int| 0 <= i0 < n as int && 0 <= j0 < n as int
                                && s[i0] == 2 && s[j0] == 1 && v == m[i0] as int + m[j0] as int;
                            let a = i0.0;
                            let b = i0.1;
                            assert(0 <= a < n as int && 0 <= b < n as int);
                            assert(s[a] == 2 && s[b] == 1);
                            assert(seen10 && seen01);
                        }
                    }
                }
            }
            -1
        } else {
            proof {
                if ans == cand11 {
                    let k = choose|k: int| 0 <= k < n as int && s[k] == 3 && cand11 == m[k];
                    assert(0 <= k < n);
                    assert(feasible_cost(m@, s@, ans as int));
                } else {
                    assert(candpair < inf);
                    let a = choose|a: int| 0 <= a < n as int && s[a] == 2 && best10 == m[a];
                    let b = choose|b: int| 0 <= b < n as int && s[b] == 1 && best01 == m[b];
                    assert(ans == best10 + best01);
                    assert(feasible_cost(m@, s@, ans as int));
                }

                assert forall|v: int| feasible_cost(m@, s@, v) implies ans as int <= v by {
                    assert(ans <= cand11 || ans <= candpair);
                    if exists|k: int| 0 <= k < n as int && s[k] == 3 && v == m[k] as int {
                        let k = choose|k: int| 0 <= k < n as int && s[k] == 3 && v == m[k] as int;
                        assert(cand11 <= m[k]);
                        assert(ans as int <= cand11 as int);
                    } else {
                        let p = choose|p: int, q: int| 0 <= p < n as int && 0 <= q < n as int
                            && s[p] == 2 && s[q] == 1 && v == m[p] as int + m[q] as int;
                        let p0 = p.0;
                        let q0 = p.1;
                        assert(candpair <= m[p0] + m[q0]);
                        assert(ans as int <= candpair as int);
                    }
                }
            }
            ans
        }
    }
}

}
