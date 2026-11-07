use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_i2max(a: int, b: int) -> int {
    if a >= b {
        a
    } else {
        b
    }
}

pub open spec fn spec_prefix_gaps_up(s: Seq<i64>, k: int) -> int
    recommends
        s.len() >= 2,
        -1 <= k <= s.len() - 2,
    decreases k + 1,
{
    if k < 0 {
        0int
    } else {
        spec_i2max(
            spec_prefix_gaps_up(s, k - 1),
            (s[k + 1] as int) - (s[k] as int),
        )
    }
}

pub open spec fn spec_min_tank_liters(s: Seq<i64>, x: int) -> int
    recommends
        s.len() >= 1,
        (s[s.len() - 1] as int) < x,
{
    if s.len() == 1 {
        spec_i2max(s[0] as int, 2 * (x - (s[0] as int)))
    } else {
        let last_st = (s.len() as int) - 1;
        let hi = last_st - 1;
        spec_i2max(
            spec_i2max(s[0] as int, spec_prefix_gaps_up(s, hi)),
            2 * (x - (s[last_st] as int)),
        )
    }
}

impl Solution {
    pub fn min_tank_liters(x: i64, a: Vec<i64>) -> (res: i64)
        requires
            1 <= a.len() <= 50,
            2 <= x <= 100,
            forall|j: int|
                0 <= j < a.len() as int - 1 ==> (#[trigger] a[j] as int) < (a[j + 1] as int),
            forall|j: int|
                0 <= j < a.len() as int ==> 0 < #[trigger] a[j] as int && (a[j] as int) < x as int,
        ensures
            res as int == spec_min_tank_liters(a@, x as int),
    {
        let n = a.len();
        let mut ans: i64 = a[0];
        let mut i: usize = 0;
        let bound = n - 1;
        while i < bound {
            let d: i64 = a[i + 1] - a[i];
            if d > ans {
                ans = d;
            }
            i = i + 1;
        }
        let d2: i64 = 2 * (x - a[n - 1]);
        if d2 > ans {
            ans = d2;
        }
        ans
    }
}

}
