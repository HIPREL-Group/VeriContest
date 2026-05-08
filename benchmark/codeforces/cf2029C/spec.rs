use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn neg_inf() -> int {
    (i32::MIN / 4) as int
}

pub open spec fn max2(a: int, b: int) -> int {
    if a >= b {
        a
    } else {
        b
    }
}

pub open spec fn rating_update(current: int, performance: int) -> int {
    if performance > current {
        current + 1
    } else if performance == current {
        current
    } else {
        current - 1
    }
}

pub open spec fn dp0(a: Seq<i32>, k: int) -> int
    recommends
        0 <= k <= a.len(),
    decreases
        k,
{
    if k <= 0 {
        0
    } else {
        rating_update(dp0(a, k - 1), a[k - 1] as int)
    }
}

pub open spec fn dp1(a: Seq<i32>, k: int) -> int
    recommends
        0 <= k <= a.len(),
    decreases
        k,
{
    if k <= 0 {
        neg_inf()
    } else {
        max2(dp1(a, k - 1), dp0(a, k - 1))
    }
}

pub open spec fn dp2(a: Seq<i32>, k: int) -> int
    recommends
        0 <= k <= a.len(),
    decreases
        k,
{
    if k <= 0 {
        neg_inf()
    } else {
        let ai = a[k - 1] as int;
        max2(
            rating_update(dp1(a, k - 1), ai),
            rating_update(dp2(a, k - 1), ai),
        )
    }
}

pub open spec fn dp_answer(a: Seq<i32>) -> int {
    let ln = a.len() as int;
    max2(dp1(a, ln), dp2(a, ln))
}

impl Solution {
    pub fn max_rating(a: Vec<i32>) -> (result: i32)
        requires
            a.len() >= 1,
            a.len() <= 300_000,
            forall |i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= a.len() as int,
        ensures
            result as int == dp_answer(a@),
    {
    }
}

}
