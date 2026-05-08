use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn num_changes(a: Seq<i32>, b: Seq<i32>) -> int
        decreases a.len(),
    {
        if a.len() == 0 || a.len() != b.len() { 0 }
        else {
            (if a.last() != b.last() { 1int } else { 0int })
                + Self::num_changes(a.drop_last(), b.drop_last())
        }
    }

    pub open spec fn seq_max(s: Seq<i32>) -> int
        decreases s.len(),
    {
        if s.len() <= 0 { i32::MIN as int }
        else if s.len() == 1 { s[0] as int }
        else {
            let rest = Self::seq_max(s.drop_last());
            if s.last() as int >= rest { s.last() as int } else { rest }
        }
    }

    pub open spec fn seq_min(s: Seq<i32>) -> int
        decreases s.len(),
    {
        if s.len() <= 0 { i32::MAX as int }
        else if s.len() == 1 { s[0] as int }
        else {
            let rest = Self::seq_min(s.drop_last());
            if (s.last() as int) <= rest { s.last() as int } else { rest }
        }
    }

    pub fn min_difference(nums: Vec<i32>) -> (res: i32)
        requires
            1 <= nums.len() <= 100_000,
            forall |i: int| 0 <= i < nums.len() ==> -1_000_000_000 <= #[trigger] nums[i] <= 1_000_000_000,
        ensures
            nums.len() <= 4 ==> res == 0,
            nums.len() > 4 ==> (
                exists |m: Seq<i32>|
                    m.len() == nums.len()
                    && Self::num_changes(nums@, m) <= 3
                    && res as int == Self::seq_max(m) - Self::seq_min(m)
                    && forall |m2: Seq<i32>|
                        m2.len() == nums.len()
                        && Self::num_changes(nums@, m2) <= 3
                        ==> Self::seq_max(m2) - Self::seq_min(m2) >= res as int
            ),
    {
    }
}

}