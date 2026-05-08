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

        while i < n {
            let gap = rungs[i] - prev;
            let added = (gap - 1) / dist;
            result = result + added;
            prev = rungs[i];
            i += 1;
        }

        result
    }
}

}
