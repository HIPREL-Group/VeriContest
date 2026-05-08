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

proof fn lemma_max_color_bounds(r: int, g: int, b: int)
    requires
        0 <= r,
        0 <= g,
        0 <= b,
    ensures
        max_color(r, g, b) <= total_balloons(r, g, b),
        0 <= total_balloons(r, g, b) - max_color(r, g, b),
{
    if r >= g {
        if r >= b {
            assert(max_color(r, g, b) == r);
        } else {
            assert(max_color(r, g, b) == b);
        }
    } else {
        if g >= b {
            assert(max_color(r, g, b) == g);
        } else {
            assert(max_color(r, g, b) == b);
        }
    }
}

proof fn lemma_impl_largest_matches_spec(r: int, g: int, b: int)
    ensures
        (if (if r >= g { r } else { g }) >= b { (if r >= g { r } else { g }) } else { b }) == max_color(r, g, b),
{
    if r >= g {
        if r >= b {
            assert((if r >= g { r } else { g }) == r);
            assert((if (if r >= g { r } else { g }) >= b { (if r >= g { r } else { g }) } else { b }) == r);
            assert(max_color(r, g, b) == r);
        } else {
            assert((if r >= g { r } else { g }) == r);
            assert((if r >= g { r } else { g }) < b);
            assert((if (if r >= g { r } else { g }) >= b { (if r >= g { r } else { g }) } else { b }) == b);
            assert(max_color(r, g, b) == b);
        }
    } else {
        if g >= b {
            assert((if r >= g { r } else { g }) == g);
            assert((if (if r >= g { r } else { g }) >= b { (if r >= g { r } else { g }) } else { b }) == g);
            assert(max_color(r, g, b) == g);
        } else {
            assert((if r >= g { r } else { g }) == g);
            assert((if r >= g { r } else { g }) < b);
            assert((if (if r >= g { r } else { g }) >= b { (if r >= g { r } else { g }) } else { b }) == b);
            assert(max_color(r, g, b) == b);
        }
    }
}

proof fn lemma_div_by_3_bounds(n: int)
    requires
        0 <= n,
    ensures
        3 * (n / 3) <= n,
        n < 3 * ((n / 3) + 1),
{
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
        proof {
            let total = total_balloons(r as int, g as int, b as int);
            lemma_max_color_bounds(r as int, g as int, b as int);
            lemma_impl_largest_matches_spec(r as int, g as int, b as int);
            lemma_div_by_3_bounds(total);
            assert(sum as int == total);
            assert(rg_max as int == if r as int >= g as int { r as int } else { g as int });
            assert(largest as int == max_color(r as int, g as int, b as int));
            assert(limit_by_total as int == total / 3);
            assert(limit_by_dominant as int == total - max_color(r as int, g as int, b as int));
        }
        if limit_by_total <= limit_by_dominant {
            proof {
                let total = total_balloons(r as int, g as int, b as int);
                assert(0 <= limit_by_total as int);
                assert(3 * (limit_by_total as int) <= total);
                assert((limit_by_total as int) <= total - max_color(r as int, g as int, b as int));
                assert forall|t: int| t > limit_by_total as int implies !feasible_tables(r as int, g as int, b as int, t) by {
                    assert(t >= limit_by_total as int + 1);
                    assert(total < 3 * (limit_by_total as int + 1));
                    assert(3 * t > total);
                }
            }
            limit_by_total
        } else {
            proof {
                let total = total_balloons(r as int, g as int, b as int);
                assert(0 <= limit_by_dominant as int);
                assert((limit_by_dominant as int) < (limit_by_total as int));
                assert(3 * (limit_by_dominant as int) < 3 * (limit_by_total as int));
                assert(3 * (limit_by_total as int) <= total);
                assert(3 * (limit_by_dominant as int) <= total);
                assert((limit_by_dominant as int) <= total - max_color(r as int, g as int, b as int));
                assert forall|t: int| t > limit_by_dominant as int implies !feasible_tables(r as int, g as int, b as int, t) by {
                    assert(t > total - max_color(r as int, g as int, b as int));
                }
            }
            limit_by_dominant
        }
    }
}

}
