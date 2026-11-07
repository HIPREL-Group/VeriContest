use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn gap(rungs: Seq<i32>, i: int) -> int {
        if i == 0 {
            rungs[0] as int
        } else {
            rungs[i] as int - rungs[i - 1] as int
        }
    }

    pub open spec fn rungs_for_gap(gap: int, dist: int) -> int {
        (gap - 1) / dist
    }

    pub open spec fn total_rungs(rungs: Seq<i32>, dist: int, n: int) -> int
        decreases n
    {
        if n <= 0 {
            0
        } else {
            Self::total_rungs(rungs, dist, n - 1) + Self::rungs_for_gap(Self::gap(rungs, n - 1), dist)
        }
    }

    pub fn add_rungs(rungs: Vec<i32>, dist: i32) -> (res: i32)
        requires
            1 <= rungs.len() <= 100_000,
            forall |i: int| 0 <= i < rungs.len() ==> 1 <= #[trigger] rungs[i] <= 1_000_000_000,
            1 <= dist <= 1_000_000_000,
            forall |i: int, j: int| 0 <= i < j < rungs.len() ==> rungs[i] < rungs[j],
        ensures
            res == Self::total_rungs(rungs@, dist as int, rungs.len() as int),
    {
        let mut result: i32 = 0;
        let mut prev: i32 = 0;
        let n = rungs.len();
        let mut i: usize = 0;

        while i < n
            invariant
                0 <= i <= n,
                n == rungs.len(),
                1 <= rungs.len() <= 100_000,
                forall |k: int| 0 <= k < rungs.len() ==> 1 <= #[trigger] rungs[k] <= 1_000_000_000,
                1 <= dist <= 1_000_000_000,
                forall |k: int, j: int| 0 <= k < j < rungs.len() ==> rungs[k] < rungs[j],
                i == 0 ==> prev == 0i32,
                i > 0 ==> prev == rungs[i as int - 1],
                result as int == Self::total_rungs(rungs@, dist as int, i as int),
                0 <= result <= prev,
            decreases n - i,
        {
            proof {
                if i > 0 {
                    assert(rungs[i as int - 1] < rungs[i as int]);
                }
            }

            let gap = rungs[i] - prev;

            assert(((gap - 1) as int) / (dist as int) <= (gap - 1) as int) by(nonlinear_arith)
                requires
                    gap as int >= 1,
                    dist as int >= 1,
            {
            }

            let added = (gap - 1) / dist;
            result = result + added;
            prev = rungs[i];
            i += 1;
        }

        result
    }
}

}
