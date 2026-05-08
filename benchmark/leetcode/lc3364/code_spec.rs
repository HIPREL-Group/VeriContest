use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn window_sum(nums: Seq<i32>, start: int, len: int) -> int
        recommends
            0 <= start,
            0 <= len,
            start + len <= nums.len(),
        decreases len
    {
        if len <= 0 {
            0
        } else {
            nums[start] as int + Self::window_sum(nums, start + 1, len - 1)
        }
    }

    pub open spec fn min_two(a: int, b: int) -> int {
        if a == -1 {
            b
        } else if b == -1 {
            a
        } else if a <= b {
            a
        } else {
            b
        }
    }

    pub open spec fn window_candidate(nums: Seq<i32>, start: int, len: int) -> int
        recommends
            0 <= start,
            0 <= len,
            start + len <= nums.len(),
    {
        let s = Self::window_sum(nums, start, len);
        if s > 0 { s } else { -1 }
    }

    pub open spec fn min_for_len_prefix(nums: Seq<i32>, len: int, count: int) -> int
        recommends
            1 <= len <= nums.len(),
            0 <= count <= nums.len() - len + 1,
        decreases count
    {
        if count <= 0 {
            -1
        } else {
            let prev = Self::min_for_len_prefix(nums, len, count - 1);
            let cand = Self::window_candidate(nums, count - 1, len);
            Self::min_two(prev, cand)
        }
    }

    pub open spec fn min_for_lengths_prefix(nums: Seq<i32>, l: int, upto: int) -> int
        recommends
            1 <= l <= nums.len(),
            l <= upto <= nums.len() + 1,
        decreases upto - l
    {
        if upto <= l {
            -1
        } else {
            let prev = Self::min_for_lengths_prefix(nums, l, upto - 1);
            let len = upto - 1;
            let all_starts = nums.len() - len + 1;
            let cur = Self::min_for_len_prefix(nums, len, all_starts);
            Self::min_two(prev, cur)
        }
    }

    pub fn minimum_sum_subarray(nums: Vec<i32>, l: i32, r: i32) -> (result: i32)
        requires
            1 <= nums.len() <= 100,
            1 <= l <= r <= nums.len(),
            forall |i: int| 0 <= i < nums.len() ==> -1000 <= #[trigger] nums[i] <= 1000,
        ensures
            result as int == Self::min_for_lengths_prefix(nums@, l as int, r as int + 1),
    {
        let n = nums.len();
        let mut best: i64 = -1;
        let mut len: usize = l as usize;
        while len <= r as usize {
            let mut start: usize = 0;
            while start + len <= n {
                let mut sum: i64 = 0;
                let mut t: usize = 0;
                while t < len {
                    sum = sum + nums[start + t] as i64;
                    t += 1;
                }
                if sum > 0 && (best == -1 || sum < best) {
                    best = sum;
                }
                start += 1;
            }
            len += 1;
        }
        best as i32
    }
}

}
