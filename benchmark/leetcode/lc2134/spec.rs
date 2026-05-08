use vstd::prelude::*;

fn main() {}

verus! {
    pub struct Solution;

    impl Solution {
        pub open spec fn count_ones(s: Seq<i32>, end: int) -> int
            decreases end
        {
            if end <= 0 { 0 }
            else {
                Self::count_ones(s, end - 1) + if s[end - 1] == 1i32 { 1int } else { 0int }
            }
        }

        pub open spec fn circ_ones(s: Seq<i32>, start: int, w: int) -> int
            decreases w
        {
            if w <= 0 { 0 }
            else {
                Self::circ_ones(s, start, w - 1) + if s[(start + w - 1) % (s.len() as int)] == 1i32 { 1int } else { 0int }
            }
        }

        pub open spec fn max_circ_ones(s: Seq<i32>, w: int, pos: int) -> int
            decreases pos
        {
            if pos <= 0 {
                Self::circ_ones(s, 0, w)
            } else {
                let prev = Self::max_circ_ones(s, w, pos - 1);
                let cur = Self::circ_ones(s, pos, w);
                if cur > prev { cur } else { prev }
            }
        }

        pub fn min_swaps(nums: Vec<i32>) -> (res: i32)
            requires
                1 <= nums.len() <= 100000,
                forall|i: int| 0 <= i < nums.len() ==> #[trigger] nums[i] == 0 || nums[i] == 1,
                exists|i: int| 0 <= i < nums.len() && nums[i] == 1,
            ensures
                res >= 0,
                res as int == Self::count_ones(nums@, nums.len() as int) - Self::max_circ_ones(nums@, Self::count_ones(nums@, nums.len() as int), nums.len() as int),
        {
        }
    }
}
