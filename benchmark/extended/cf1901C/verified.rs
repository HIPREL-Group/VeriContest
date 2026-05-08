use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn halving_steps(d: int) -> int
    decreases d
{
    if d <= 0 { 0 } else { 1 + halving_steps(d / 2) }
}

pub open spec fn is_min_max_of(a: Seq<i64>, mn: int, mx: int) -> bool {
    a.len() >= 1
    && (forall|i: int| 0 <= i < a.len() ==> mn <= #[trigger] (a[i] as int) <= mx)
    && (exists|i: int| 0 <= i < a.len() && a[i] as int == mn)
    && (exists|i: int| 0 <= i < a.len() && a[i] as int == mx)
}

pub struct Solution;

impl Solution {
    pub fn steps_from_diff(d: i64) -> (res: i64)
        requires
            d >= 0,
        ensures
            res >= 0,
            res <= d,
            res as int == halving_steps(d as int),
        decreases d,
    {
        if d == 0 {
            0
        } else {
            let sub = Self::steps_from_diff(d / 2);
            proof {
                assert(d / 2 + 1 <= d);
            }
            sub + 1
        }
    }

    pub fn min_operations(a: Vec<i64>) -> (result: i64)
        requires
            1 <= a.len() <= 200_000,
            forall|i: int| 0 <= i < a.len() ==> 0 <= #[trigger] a[i] <= 1_000_000_000,
        ensures
            result >= 0,
            exists|mn: int, mx: int|
                is_min_max_of(a@, mn, mx)
                && result as int == halving_steps(mx - mn),
    {
        let n = a.len();
        let mut mn = a[0];
        let mut mx = a[0];
        let mut i: usize = 1;
        while i < n
            invariant
                1 <= i <= n,
                n == a.len(),
                forall|j: int| 0 <= j < n ==> 0 <= #[trigger] a[j] <= 1_000_000_000,
                forall|j: int| 0 <= j < i ==> mn <= #[trigger] a[j],
                forall|j: int| 0 <= j < i ==> #[trigger] a[j] <= mx,
                exists|j: int| 0 <= j < i && a[j] == mn,
                exists|j: int| 0 <= j < i && a[j] == mx,
            decreases n - i,
        {
            let cur = a[i];
            if cur < mn {
                mn = cur;
            }
            if cur > mx {
                mx = cur;
            }
            i += 1;
        }
        let result = Self::steps_from_diff(mx - mn);
        proof {
            assert(i == n);
            assert(is_min_max_of(a@, mn as int, mx as int));
            assert(exists|mn0: int, mx0: int|
                is_min_max_of(a@, mn0, mx0)
                && result as int == halving_steps(mx0 - mn0)) by {
                let mn0 = mn as int;
                let mx0 = mx as int;
                assert(is_min_max_of(a@, mn0, mx0));
                assert(result as int == halving_steps((mx - mn) as int));
                assert((mx - mn) as int == mx0 - mn0);
            }
        }

        Self::steps_from_diff(mx - mn)
    }
}

}
