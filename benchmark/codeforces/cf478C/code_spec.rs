use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn total_balloons(r: int, g: int, b: int) -> int {
    r + g + b
}

pub open spec fn max_color(r: int, g: int, b: int) -> int {
    if r >= g {
        if r >= b { r } else { b }
    } else {
        if g >= b { g } else { b }
    }
}

pub open spec fn feasible_tables(r: int, g: int, b: int, t: int) -> bool {
    &&& 0 <= t
    &&& 3 * t <= total_balloons(r, g, b)
    &&& t <= total_balloons(r, g, b) - max_color(r, g, b)
}

impl Solution {
    pub fn max_decorated_tables(r: i64, g: i64, b: i64) -> (result: i64)
        requires
            0 <= r <= 2_000_000_000,
            0 <= g <= 2_000_000_000,
            0 <= b <= 2_000_000_000,
        ensures
            feasible_tables(r as int, g as int, b as int, result as int),
            forall|t: int| t > result as int ==> !feasible_tables(r as int, g as int, b as int, t),
    {
        let sum = r + g + b;
        let rg_max = if r >= g { r } else { g };
        let largest = if rg_max >= b { rg_max } else { b };
        let limit_by_total = sum / 3;
        let limit_by_dominant = sum - largest;
        if limit_by_total <= limit_by_dominant {
            limit_by_total
        } else {
            limit_by_dominant
        }
    }
}

}
