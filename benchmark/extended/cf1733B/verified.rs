use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn league_lo(x: i64, y: i64) -> int {
    if x < y {
        x as int
    } else {
        y as int
    }
}

pub open spec fn league_hi(x: i64, y: i64) -> int {
    if x > y {
        x as int
    } else {
        y as int
    }
}

pub open spec fn league_feasible(n: i64, x: i64, y: i64) -> bool {
    let n = n as int;
    let lo = league_lo(x, y);
    let hi = league_hi(x, y);
    lo == 0
        && hi > 0
        && (n - 1) % hi == 0
}

pub open spec fn spec_win_at(n: i64, hi: int, i: int) -> int
    recommends
        0 <= i < n as int - 1,
{
    2 + (i / hi) * hi
}

impl Solution {
    pub fn rule_of_league(n: i64, x: i64, y: i64) -> (r: Option<Vec<i64>>)
        requires
            2 <= n <= 100_000,
            0 <= x < n,
            0 <= y < n,
        ensures
            r == None::<Vec<i64>> <==> !league_feasible(n, x, y),
            r != None::<Vec<i64>> <==> {
                &&& league_feasible(n, x, y)
                &&& r->0@.len() == (n as int) - 1
                &&& forall|i: int|
                    #![trigger r->0@[i]]
                    0 <= i < r->0@.len() ==> r->0@[i] as int == spec_win_at(n, league_hi(x, y), i)
            },
    {
        let lo = if x < y { x } else { y };
        let hi = if x > y { x } else { y };
        if lo != 0 {
            proof {
                assert(league_lo(x, y) == lo as int);
                assert(lo as int != 0);
                assert(!league_feasible(n, x, y));
            }
            return None;
        }
        if hi == 0 {
            proof {
                assert(league_hi(x, y) == hi as int);
                assert(!league_feasible(n, x, y));
            }
            return None;
        }
        if (n - 1) % hi != 0 {
            proof {
                assert(league_hi(x, y) == hi as int);
                assert((n as int - 1) % (hi as int) != 0);
                assert(!league_feasible(n, x, y));
            }
            return None;
        }
        proof {
            assert(league_lo(x, y) == 0);
            assert(league_hi(x, y) == hi as int);
            assert(hi as int > 0);
            assert((n as int - 1) % (hi as int) == 0);
            assert(league_feasible(n, x, y));
        }
        let m = (n - 1) as usize;
        let mut w: Vec<i64> = Vec::new();
        let mut i: usize = 0;
        while i < m
            invariant
                2 <= n <= 100_000,
                0 <= x < n,
                0 <= y < n,
                m == (n - 1) as usize,
                hi == league_hi(x, y) as i64,
                league_feasible(n, x, y),
                1 <= hi,
                i <= m,
                w@.len() == i as int,
                forall|j: int|
                    #![trigger w@[j]]
                    0 <= j < i as int ==> w@[j] as int == spec_win_at(n, hi as int, j),
            decreases m - i,
        {
            let ii = i as i64;
            let block = ii / hi;
            proof {
                assert(i < m);
                assert(m == (n - 1) as usize);
                assert((i as int) < (n as int) - 1);
                if x > y {
                    assert(hi == x);
                } else {
                    assert(hi == y);
                }
                assert(hi < n);
                assert(1 <= hi <= 100_000);
                assert(0 <= ii);
                assert((ii as int) <= (n as int) - 2);
                assert(block <= ii);
                assert(block * hi <= ii * hi) by (nonlinear_arith)
                    requires
                        block <= ii,
                        hi >= 0,
                {
                }
                assert(ii * hi <= (n - 2) * (n - 1)) by (nonlinear_arith)
                    requires
                        ii <= n - 2,
                        hi < n,
                        ii >= 0,
                        hi >= 0,
                        n >= 2,
                {
                }
                assert((n - 2) * (n - 1) <= 100_000 * 100_000) by (nonlinear_arith)
                    requires
                        n <= 100_000,
                        n >= 2,
                {
                }
                assert(block * hi <= 100_000 * 100_000);
                assert(2 + block * hi < 9223372036854775807);
            }
            let win = 2 + block * hi;
            proof {
                assert((ii as int) / (hi as int) == block as int);
                assert(2 + (block as int) * (hi as int) == spec_win_at(n, hi as int, i as int));
                assert(win as int == spec_win_at(n, hi as int, i as int));
            }
            let ghost prefix = w@;
            w.push(win);
            proof {
                assert(w@ == prefix.push(win));
                assert forall|j: int|
                    0 <= j < i as int implies #[trigger] w@[j] as int == spec_win_at(n, hi as int, j) by {
                    assert(j < prefix.len());
                    assert(w@[j] == prefix[j]);
                    assert(prefix[j] as int == spec_win_at(n, hi as int, j));
                }
                assert(w@[i as int] as int == spec_win_at(n, hi as int, i as int));
                assert forall|j: int|
                    0 <= j < (i + 1) as int implies w@[j] as int == spec_win_at(n, hi as int, j) by {
                    if j < i as int {
                        assert(w@[j] as int == spec_win_at(n, hi as int, j));
                    } else {
                        assert(j == i as int);
                        assert(w@[j] as int == spec_win_at(n, hi as int, j));
                    }
                }
            }
            i = i + 1;
        }
        proof {
            assert(i == m);
            assert(w@.len() == (n as int) - 1);
            assert forall|j: int| 0 <= j < w@.len() implies w@[j] as int == spec_win_at(n, league_hi(x, y), j) by {
                assert(0 <= j && j < (n as int) - 1);
                assert(w@[j] as int == spec_win_at(n, hi as int, j));
                assert(league_hi(x, y) == hi as int);
            }
        }
        let out = Some(w);
        proof {
            assert(out != None::<Vec<i64>>);
            assert(league_feasible(n, x, y));
            assert(out->0@.len() == (n as int) - 1);
            assert forall|j: int| 0 <= j < out->0@.len() implies out->0@[j] as int == spec_win_at(n, league_hi(x, y), j) by {
                assert(out->0@ == w@);
            }
        }
        out
    }
}

}
