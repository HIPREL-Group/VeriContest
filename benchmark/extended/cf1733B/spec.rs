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
    }
}

}
