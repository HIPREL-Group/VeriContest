use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_bus_leg(a: int, f: int, i: int) -> (int, int) {
    if i % 2 == 0 {
        (f, a - f)
    } else {
        (a - f, f)
    }
}

pub open spec fn spec_bus_min_refuels_inner(a: int, b: int, f: int, k: int, i: int, have: int, ans: int) -> int
    recommends
        0 < f < a,
        1 <= b,
        1 <= k,
        0 <= i <= k,
        0 <= have,
        0 <= ans,
    decreases
        k - i,
{
    if i >= k {
        ans
    } else {
        let (x, y) = spec_bus_leg(a, f, i);
        if have < x {
            -1
        } else {
            let have1 = have - x;
            let (have_mid, ans1) = if i < k - 1 {
                if have1 < y {
                    (b, ans + 1)
                } else if have1 < 2 * y {
                    (b, ans + 1)
                } else {
                    (have1, ans)
                }
            } else {
                if have1 < y {
                    (b, ans + 1)
                } else {
                    (have1, ans)
                }
            };
            if have_mid < y {
                -1
            } else {
                spec_bus_min_refuels_inner(a, b, f, k, i + 1, have_mid - y, ans1)
            }
        }
    }
}

pub open spec fn spec_bus_min_refuels(a: int, b: int, f: int, k: int) -> int
    recommends
        0 < f < a,
        1 <= b,
        1 <= k,
{
    spec_bus_min_refuels_inner(a, b, f, k, 0, b, 0)
}

pub open spec fn spec_journey_leg_partitions_route(a: int, f: int, s: int) -> bool {
    let p = spec_bus_leg(a, f, s);
    p.0 + p.1 == a && p.0 > 0 && p.1 > 0
}

impl Solution {
    #[verifier::exec_allows_no_decreases_clause]
    pub fn min_bus_refuels(a: i64, b: i64, f: i64, k: usize) -> (r: i64)
        requires
            0 < f < a <= 1_000_000,
            1 <= b <= 1_000_000_000,
            1 <= k <= 10_000,
        ensures
            r as int == spec_bus_min_refuels(a as int, b as int, f as int, k as int),
            (r as int) == -1 || (0 <= r as int && r as int <= (k as int)),
            forall|s: int|
                #![trigger spec_bus_leg(a as int, f as int, s)]
                0 <= s < k as int ==> spec_journey_leg_partitions_route(a as int, f as int, s),
    {
        let mut ans: i64 = 0;
        let mut have: i64 = b;
        let mut i: usize = 0;
        while i < k {
            let x: i64;
            let y: i64;
            if i % 2 == 0 {
                x = f;
                y = a - f;
            } else {
                x = a - f;
                y = f;
            }
            if have < x {
                return -1;
            }
            have = have - x;
            if i < k - 1 {
                if have < y {
                    ans = ans + 1;
                    have = b;
                } else if have < 2 * y {
                    ans = ans + 1;
                    have = b;
                }
            } else {
                if have < y {
                    ans = ans + 1;
                    have = b;
                }
            }
            if have < y {
                return -1;
            }
            have = have - y;
            i = i + 1;
        }
        ans
    }
}

}
