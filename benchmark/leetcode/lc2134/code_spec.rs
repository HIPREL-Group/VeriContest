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
            let mut total_ones: usize = 0;
            let mut i: usize = 0;
            while i < nums.len() {
                if nums[i] == 1 {
                    total_ones = total_ones + 1;
                }
                i = i + 1;
            }
            
            let window_size: usize = total_ones;
            let mut ones_in_window: usize = 0;
            
            i = 0;
            while i < window_size {
                if nums[i] == 1 {
                    ones_in_window = ones_in_window + 1;
                }
                i = i + 1;
            }
            
            let mut max_ones = ones_in_window;
            
            let n = nums.len();
            i = 0;
            while i < n {
                if nums[i] == 1 && ones_in_window > 0 {
                    ones_in_window = ones_in_window - 1;
                }
                let next_idx = (i + window_size) % n;
                if nums[next_idx] == 1 {
                    ones_in_window = ones_in_window + 1;
                }
                if ones_in_window > max_ones {
                    max_ones = ones_in_window;
                }
                i = i + 1;
            }
            
            if total_ones >= max_ones {
                (total_ones - max_ones) as i32
            } else {
                0i32
            }
        }
    }
}
