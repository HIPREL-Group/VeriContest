use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_factor_at(a: Seq<i64>, bump: int, k: int) -> int
    recommends
        0 <= k && k < a.len(),
{
    if k == bump {
        a[k] as int + 1
    } else {
        a[k] as int
    }
}

pub open spec fn spec_prefix_with_bump(a: Seq<i64>, bump: int, until: int) -> int
    recommends
        0 <= until && until <= a.len() && a.len() <= 9,
{
    if until == 0 {
        1
    } else if until == 1 {
        spec_factor_at(a, bump, 0)
    } else if until == 2 {
        spec_factor_at(a, bump, 0) * spec_factor_at(a, bump, 1)
    } else if until == 3 {
        spec_factor_at(a, bump, 0) * spec_factor_at(a, bump, 1) * spec_factor_at(a, bump, 2)
    } else if until == 4 {
        spec_factor_at(a, bump, 0) * spec_factor_at(a, bump, 1) * spec_factor_at(a, bump, 2)
            * spec_factor_at(a, bump, 3)
    } else if until == 5 {
        spec_factor_at(a, bump, 0) * spec_factor_at(a, bump, 1) * spec_factor_at(a, bump, 2)
            * spec_factor_at(a, bump, 3) * spec_factor_at(a, bump, 4)
    } else if until == 6 {
        spec_factor_at(a, bump, 0) * spec_factor_at(a, bump, 1) * spec_factor_at(a, bump, 2)
            * spec_factor_at(a, bump, 3) * spec_factor_at(a, bump, 4) * spec_factor_at(a, bump, 5)
    } else if until == 7 {
        spec_factor_at(a, bump, 0) * spec_factor_at(a, bump, 1) * spec_factor_at(a, bump, 2)
            * spec_factor_at(a, bump, 3) * spec_factor_at(a, bump, 4) * spec_factor_at(a, bump, 5)
            * spec_factor_at(a, bump, 6)
    } else if until == 8 {
        spec_factor_at(a, bump, 0) * spec_factor_at(a, bump, 1) * spec_factor_at(a, bump, 2)
            * spec_factor_at(a, bump, 3) * spec_factor_at(a, bump, 4) * spec_factor_at(a, bump, 5)
            * spec_factor_at(a, bump, 6) * spec_factor_at(a, bump, 7)
    } else {
        spec_factor_at(a, bump, 0) * spec_factor_at(a, bump, 1) * spec_factor_at(a, bump, 2)
            * spec_factor_at(a, bump, 3) * spec_factor_at(a, bump, 4) * spec_factor_at(a, bump, 5)
            * spec_factor_at(a, bump, 6) * spec_factor_at(a, bump, 7) * spec_factor_at(a, bump, 8)
    }
}

pub open spec fn spec_product_with_bump_at(a: Seq<i64>, bump: int) -> int
    recommends
        0 <= bump && bump < a.len(),
        a.len() <= 9,
{
    spec_prefix_with_bump(a, bump, a.len() as int)
}

pub open spec fn spec_max2(x: int, y: int) -> int {
    if x > y {
        x
    } else {
        y
    }
}

pub open spec fn spec_max_bumps_upto(a: Seq<i64>, end: int) -> int
    recommends
        0 <= end && end <= a.len() && a.len() <= 9,
{
    if end == 0 {
        0
    } else if end == 1 {
        spec_product_with_bump_at(a, 0)
    } else if end == 2 {
        spec_max2(spec_product_with_bump_at(a, 0), spec_product_with_bump_at(a, 1))
    } else if end == 3 {
        spec_max2(
            spec_max2(spec_product_with_bump_at(a, 0), spec_product_with_bump_at(a, 1)),
            spec_product_with_bump_at(a, 2),
        )
    } else if end == 4 {
        spec_max2(
            spec_max2(
                spec_max2(spec_product_with_bump_at(a, 0), spec_product_with_bump_at(a, 1)),
                spec_product_with_bump_at(a, 2),
            ),
            spec_product_with_bump_at(a, 3),
        )
    } else if end == 5 {
        spec_max2(
            spec_max2(
                spec_max2(
                    spec_max2(spec_product_with_bump_at(a, 0), spec_product_with_bump_at(a, 1)),
                    spec_product_with_bump_at(a, 2),
                ),
                spec_product_with_bump_at(a, 3),
            ),
            spec_product_with_bump_at(a, 4),
        )
    } else if end == 6 {
        spec_max2(
            spec_max2(
                spec_max2(
                    spec_max2(
                        spec_max2(spec_product_with_bump_at(a, 0), spec_product_with_bump_at(a, 1)),
                        spec_product_with_bump_at(a, 2),
                    ),
                    spec_product_with_bump_at(a, 3),
                ),
                spec_product_with_bump_at(a, 4),
            ),
            spec_product_with_bump_at(a, 5),
        )
    } else if end == 7 {
        spec_max2(
            spec_max2(
                spec_max2(
                    spec_max2(
                        spec_max2(
                            spec_max2(spec_product_with_bump_at(a, 0), spec_product_with_bump_at(a, 1)),
                            spec_product_with_bump_at(a, 2),
                        ),
                        spec_product_with_bump_at(a, 3),
                    ),
                    spec_product_with_bump_at(a, 4),
                ),
                spec_product_with_bump_at(a, 5),
            ),
            spec_product_with_bump_at(a, 6),
        )
    } else if end == 8 {
        spec_max2(
            spec_max2(
                spec_max2(
                    spec_max2(
                        spec_max2(
                            spec_max2(
                                spec_max2(spec_product_with_bump_at(a, 0), spec_product_with_bump_at(a, 1)),
                                spec_product_with_bump_at(a, 2),
                            ),
                            spec_product_with_bump_at(a, 3),
                        ),
                        spec_product_with_bump_at(a, 4),
                    ),
                    spec_product_with_bump_at(a, 5),
                ),
                spec_product_with_bump_at(a, 6),
            ),
            spec_product_with_bump_at(a, 7),
        )
    } else {
        spec_max2(
            spec_max2(
                spec_max2(
                    spec_max2(
                        spec_max2(
                            spec_max2(
                                spec_max2(
                                    spec_max2(spec_product_with_bump_at(a, 0), spec_product_with_bump_at(a, 1)),
                                    spec_product_with_bump_at(a, 2),
                                ),
                                spec_product_with_bump_at(a, 3),
                            ),
                            spec_product_with_bump_at(a, 4),
                        ),
                        spec_product_with_bump_at(a, 5),
                    ),
                    spec_product_with_bump_at(a, 6),
                ),
                spec_product_with_bump_at(a, 7),
            ),
            spec_product_with_bump_at(a, 8),
        )
    }
}

impl Solution {
    pub fn max_product_one_increment(a: Vec<i64>) -> (res: i64)
        requires
            1 <= a.len() && a.len() <= 9,
            forall|k: int| 0 <= k < a.len() ==> 0 <= #[trigger] a[k] && a[k] <= 9,
        ensures
            res as int == spec_max_bumps_upto(a@, a.len() as int),
    {
        let n = a.len();
        let mut best: i64 = 0;
        let mut i: usize = 0;
        while i < n {
            let mut p: i64 = 1;
            let mut j: usize = 0;
            while j < n {
                if j == i {
                    p = p * (a[j] + 1);
                } else {
                    p = p * a[j];
                }
                j = j + 1;
            }
            if p > best {
                best = p;
            }
            i = i + 1;
        }
        best
    }
}

}
