use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_dp0(row0: Seq<i64>, row1: Seq<i64>, j: int) -> bool
        recommends
            row0.len() == row1.len(),
            0 <= j < row0.len(),
        decreases j,
    {
        if j <= 0 {
            row0[0] == 1
        } else if row0[j] == 1 && row1[j] == 0 {
            Self::spec_dp0(row0, row1, j - 1)
        } else if row0[j] == 0 && row1[j] == 1 {
            false
        } else {
            Self::spec_dp1(row0, row1, j - 1)
        }
    }

    pub open spec fn spec_dp1(row0: Seq<i64>, row1: Seq<i64>, j: int) -> bool
        recommends
            row0.len() == row1.len(),
            0 <= j < row0.len(),
        decreases j,
    {
        if j <= 0 {
            row1[0] == 1
        } else if row0[j] == 1 && row1[j] == 0 {
            false
        } else if row0[j] == 0 && row1[j] == 1 {
            Self::spec_dp1(row0, row1, j - 1)
        } else {
            Self::spec_dp0(row0, row1, j - 1)
        }
    }

    pub fn can_paint_wall(m: usize, row0: Vec<i64>, row1: Vec<i64>) -> (result: bool)
        requires
            m >= 1,
            row0.len() == m,
            row1.len() == m,
            forall |k: int| 0 <= k < m as int ==> (#[trigger] row0[k] == 0 || row0[k] == 1),
            forall |k: int| 0 <= k < m as int ==> (#[trigger] row1[k] == 0 || row1[k] == 1),
            forall |k: int| 0 <= k < m as int ==> (#[trigger] row0[k] == 1 || row1[k] == 1),
        ensures
            result == (Self::spec_dp0(row0@, row1@, m as int - 1) || Self::spec_dp1(row0@, row1@, m as int - 1)),
    {
        let mut dp0: bool;
        let mut dp1: bool;
        if row0[0] == 1 && row1[0] == 0 {
            dp0 = true;
            dp1 = false;
        } else if row0[0] == 0 && row1[0] == 1 {
            dp0 = false;
            dp1 = true;
        } else {
            dp0 = true;
            dp1 = true;
        }
        let mut j: usize = 1;
        while j < m
            invariant
                1 <= j <= m,
                m >= 1,
                row0.len() == m,
                row1.len() == m,
                forall |k: int| 0 <= k < m as int ==> (#[trigger] row0[k] == 0 || row0[k] == 1),
                forall |k: int| 0 <= k < m as int ==> (#[trigger] row1[k] == 0 || row1[k] == 1),
                forall |k: int| 0 <= k < m as int ==> (#[trigger] row0[k] == 1 || row1[k] == 1),
                dp0 == Self::spec_dp0(row0@, row1@, j as int - 1),
                dp1 == Self::spec_dp1(row0@, row1@, j as int - 1),
            decreases m - j,
        {
            let new_dp0: bool;
            let new_dp1: bool;
            if row0[j] == 1 && row1[j] == 0 {
                new_dp0 = dp0;
                new_dp1 = false;
            } else if row0[j] == 0 && row1[j] == 1 {
                new_dp0 = false;
                new_dp1 = dp1;
            } else {
                new_dp0 = dp1;
                new_dp1 = dp0;
            }
            dp0 = new_dp0;
            dp1 = new_dp1;
            j = j + 1;
        }
        dp0 || dp1
    }
}

}
