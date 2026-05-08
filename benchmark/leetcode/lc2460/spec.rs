use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn op_step(s: Seq<i32>, i: int) -> Seq<i32>
    {
        if 0 <= i + 1 < s.len() && s[i] == s[i + 1] {
            s.update(i, ((s[i] as int) * 2) as i32).update(i + 1, 0)
        } else {
            s
        }
    }

    pub open spec fn apply_ops_prefix(s: Seq<i32>, upto: int) -> Seq<i32>
        decreases upto,
    {
        if upto <= 0 || s.len() < 2 {
            s
        } else {
            let prev = Self::apply_ops_prefix(s, upto - 1);
            Self::op_step(prev, upto - 1)
        }
    }

    pub open spec fn nonzero_prefix(s: Seq<i32>, end: int) -> Seq<i32>
        decreases end,
    {
        if end <= 0 {
            seq![]
        } else if end > s.len() {
            Self::nonzero_prefix(s, s.len() as int)
        } else {
            let prev = Self::nonzero_prefix(s, end - 1);
            if s[end - 1] != 0 {
                prev.push(s[end - 1])
            } else {
                prev
            }
        }
    }

    pub open spec fn extend_with_zeros(base: Seq<i32>, total: int) -> Seq<i32>
        decreases total - base.len(),
    {
        if total <= base.len() {
            base
        } else {
            Self::extend_with_zeros(base, total - 1).push(0)
        }
    }

    pub open spec fn apply_operations_model(s: Seq<i32>) -> Seq<i32>
    {
        let transformed = Self::apply_ops_prefix(s, s.len() - 1);
        let nonz = Self::nonzero_prefix(transformed, transformed.len() as int);
        Self::extend_with_zeros(nonz, transformed.len() as int)
    }

    pub fn apply_operations(nums: Vec<i32>) -> (result: Vec<i32>)
        requires
            2 <= nums.len() <= 2000,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1000,
        ensures
            result@ == Self::apply_operations_model(nums@),
    {
    }
}

}
