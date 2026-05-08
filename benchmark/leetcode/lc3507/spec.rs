use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_non_decreasing(s: Seq<i32>) -> bool {
        forall |i: int| 0 < i && i < s.len() ==> s[i - 1] <= #[trigger] s[i]
    }

    pub open spec fn pair_sum(s: Seq<i32>, i: int) -> int {
        if 0 <= i && i + 1 < s.len() {
            s[i] as int + s[i + 1] as int
        } else {
            0
        }
    }

    pub open spec fn pair_sum_i32(s: Seq<i32>, i: int) -> i32 {
        if 0 <= i && i + 1 < s.len() {
            ((s[i] as i64 + s[i + 1] as i64) as i32)
        } else {
            0
        }
    }

    pub open spec fn min_index_prefix(s: Seq<i32>, upto: int) -> int
        decreases upto,
    {
        if s.len() < 2 || upto <= 1 {
            0
        } else {
            let prev = Self::min_index_prefix(s, upto - 1);
            let cur = upto - 1;
            if Self::pair_sum(s, cur) < Self::pair_sum(s, prev) {
                cur
            } else {
                prev
            }
        }
    }

    pub open spec fn min_pair_index(s: Seq<i32>) -> int {
        if s.len() < 2 {
            0
        } else {
            Self::min_index_prefix(s, s.len() - 1)
        }
    }

    pub open spec fn merge_at(s: Seq<i32>, idx: int) -> Seq<i32> {
        if s.len() < 2 {
            s
        } else if 0 <= idx && idx + 1 < s.len() {
            s.subrange(0, idx) + seq![Self::pair_sum_i32(s, idx)] + s.subrange(idx + 2, s.len() as int)
        } else {
            s.subrange(0, 0) + seq![Self::pair_sum_i32(s, 0)] + s.subrange(2, s.len() as int)
        }
    }

    pub open spec fn next_seq(s: Seq<i32>) -> Seq<i32> {
        if s.len() < 2 {
            s
        } else {
            Self::merge_at(s, Self::min_pair_index(s))
        }
    }

    pub open spec fn steps_to_sort_fuel(s: Seq<i32>, fuel: nat) -> nat
        decreases fuel,
    {
        if fuel == 0 || s.len() <= 1 || Self::is_non_decreasing(s) {
            0
        } else {
            1nat + Self::steps_to_sort_fuel(Self::next_seq(s), (fuel - 1) as nat)
        }
    }

    pub open spec fn steps_to_sort(s: Seq<i32>) -> nat {
        Self::steps_to_sort_fuel(s, s.len() as nat)
    }

    pub fn minimum_pair_removal(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 50,
            forall |i: int| 0 <= i < nums.len() ==> -1000 <= #[trigger] nums[i] <= 1000,
        ensures
            result as int == Self::steps_to_sort(nums@) as int,
    {
    }
}

}
