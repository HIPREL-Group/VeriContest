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
    fn rating_step(cur: i32, perf: i32) -> (y: i32)
        ensures
            y as int == rating_update(cur as int, perf as int),
    {
        if perf > cur {
            cur + 1
        } else if perf < cur {
            cur - 1
        } else {
            cur
        }
    }

    pub fn max_rating(a: Vec<i32>) -> (result: i32)
        requires
            a.len() >= 1,
            a.len() <= 300_000,
            forall |i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= a.len() as int,
        ensures
            result as int == dp_answer(a@),
    {
        let n = a.len();
        let neg: i32 = i32::MIN / 4;
        let mut f0: i32 = 0;
        let mut f1: i32 = neg;
        let mut f2: i32 = neg;
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                n == a.len(),
                n >= 1,
                n <= 300_000,
                forall |j: int| 0 <= j < a.len() ==> 1 <= #[trigger] a[j] <= a.len() as int,
                f0 as int == #[trigger] dp0(a@, i as int),
                f1 as int == #[trigger] dp1(a@, i as int),
                f2 as int == #[trigger] dp2(a@, i as int),
            decreases n - i,
        {
            let ai = a[i];
            proof {
                reveal_with_fuel(dp0, 2);
                reveal_with_fuel(dp1, 2);
                reveal_with_fuel(dp2, 2);
            }
            let new_f2 = Self::rating_step(f1, ai).max(Self::rating_step(f2, ai));
            let new_f1 = f1.max(f0);
            let new_f0 = Self::rating_step(f0, ai);
            f2 = new_f2;
            f1 = new_f1;
            f0 = new_f0;
            i = i + 1;
        }
        proof {
            assert(i == n);
            assert(f0 as int == dp0(a@, a.len() as int));
            assert(f1 as int == dp1(a@, a.len() as int));
            assert(f2 as int == dp2(a@, a.len() as int));
        }
        let res = f1.max(f2);
        proof {
            assert(res as int == dp_answer(a@));
        }
        res
    }
}

}
