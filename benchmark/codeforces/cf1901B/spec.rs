use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn start_teleports(c: Seq<i64>) -> int
        recommends
            c.len() >= 1,
    {
        c[0] as int - 1
    }

    pub open spec fn pos_step(c: Seq<i64>, i: int) -> int
        recommends
            c.len() >= 2,
            0 <= i < c.len() - 1,
    {
        let a = c[i + 1] as int;
        let b = c[i] as int;
        if a > b {
            a - b
        } else {
            0
        }
    }

    pub open spec fn spec_gap_sum(c: Seq<i64>, k: int) -> int
        recommends
            c.len() >= 1,
            0 <= k <= c.len() - 1,
            k > 0 ==> c.len() >= 2,
        decreases k,
    {
        if k <= 0 {
            0
        } else {
            Self::spec_gap_sum(c, k - 1) + Self::pos_step(c, k - 1)
        }
    }

    pub fn min_chip_teleports(c: Vec<i64>) -> (res: i64)
        requires
            1 <= c.len() <= 200_000,
            forall|i: int|
                0 <= i < c.len() as int ==> 0 <= #[trigger] c[i] as int <= 1_000_000_000,
            c[0] as int >= 1,
        ensures
            res as int == Self::start_teleports(c@) + Self::spec_gap_sum(c@, (c.len() as int) - 1),
            forall|i: int|
                0 <= i < c.len() as int - 1 ==> #[trigger] Self::pos_step(c@, i) >= 0,
    {
    }
}

}
