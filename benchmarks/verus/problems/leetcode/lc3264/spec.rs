use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn to_int_seq(s: Seq<i32>) -> Seq<int> {
        Seq::new(s.len(), |i: int| s[i] as int)
    }

    pub open spec fn min_index_prefix(s: Seq<int>, end: int) -> int
        decreases end,
    {
        if end <= 1 {
            0
        } else {
            let j = Self::min_index_prefix(s, end - 1);
            if s[end - 1] < s[j] {
                end - 1
            } else {
                j
            }
        }
    }

    pub open spec fn apply_once(s: Seq<int>, multiplier: int) -> Seq<int> {
        if s.len() == 0 {
            s
        } else {
            let idx = Self::min_index_prefix(s, s.len() as int);
            s.update(idx, s[idx] * multiplier)
        }
    }

    pub open spec fn after_k(s: Seq<int>, k: int, multiplier: int) -> Seq<int>
        decreases k,
    {
        if k <= 0 {
            s
        } else {
            Self::apply_once(Self::after_k(s, k - 1, multiplier), multiplier)
        }
    }

    pub fn get_final_state(nums: Vec<i32>, k: i32, multiplier: i32) -> (result: Vec<i32>)
        requires
            1 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
            1 <= k <= 10,
            1 <= multiplier <= 5,
        ensures
            result.len() == nums.len(),
            forall |i: int| 0 <= i < result.len() ==> {
                &&& 1 <= #[trigger] result[i]
                &&& result[i] as int == Self::after_k(Self::to_int_seq(nums@), k as int, multiplier as int)[i]
            },
    {
    }
}

}
