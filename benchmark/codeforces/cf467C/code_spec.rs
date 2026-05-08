use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn start_count(nums: Seq<i64>, m: int) -> int {
        if 0 < m <= nums.len() {
            nums.len() - m + 1
        } else {
            0
        }
    }

    pub open spec fn window_sum(nums: Seq<i64>, start: int, len: int) -> int
        decreases if len > 0 { len } else { 0 },
    {
        if len <= 0 || start < 0 || start + len > nums.len() {
            0
        } else {
            Self::window_sum(nums, start, len - 1) + nums[start + len - 1] as int
        }
    }

    pub open spec fn chosen_sum(nums: Seq<i64>, m: int, starts: Seq<int>) -> int
        decreases starts.len(),
    {
        if starts.len() == 0 {
            0
        } else {
            Self::window_sum(nums, starts[0], m) + Self::chosen_sum(nums, m, starts.drop_first())
        }
    }

    pub open spec fn admissible_from(nums: Seq<i64>, m: int, left: int, pos: int, starts: Seq<int>) -> bool
    {
        &&& starts.len() == left
        &&& 0 <= left
        &&& 0 <= pos
        &&& 0 < m <= nums.len()
        &&& forall |i: int| 0 <= i < starts.len() ==> pos <= #[trigger] starts[i] < Self::start_count(nums, m)
        &&& forall |i: int, j: int| 0 <= i < j < starts.len() ==> #[trigger] starts[i] + m <= #[trigger] starts[j]
    }

    pub open spec fn admissible_starts(nums: Seq<i64>, m: int, k: int, starts: Seq<int>) -> bool
    {
        Self::admissible_from(nums, m, k, 0, starts)
    }

    pub open spec fn best_sum_from(nums: Seq<i64>, m: int, left: int, pos: int) -> int
        decreases if left > 0 { left } else { 0 }, if pos <= Self::start_count(nums, m) { Self::start_count(nums, m) - pos } else { 0 },
    {
        if left <= 0 || pos < 0 {
            0
        } else if pos >= Self::start_count(nums, m) {
            -1
        } else {
            let skip = Self::best_sum_from(nums, m, left, pos + 1);
            let tail = Self::best_sum_from(nums, m, left - 1, pos + m);
            let take = if tail < 0 { -1 } else { Self::window_sum(nums, pos, m) + tail };
            if skip >= take { skip } else { take }
        }
    }

    pub fn max_k_segments_sum(nums: Vec<i64>, m: usize, k: usize) -> (result: i128)
        requires
            1 <= nums.len() <= 5000,
            1 <= m <= nums.len(),
            1 <= k,
            m * k <= nums.len(),
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1_000_000_000,
        ensures
            exists |starts: Seq<int>|
                Self::admissible_starts(nums@, m as int, k as int, starts)
                && result as int == #[trigger] Self::chosen_sum(nums@, m as int, starts),
            forall |starts: Seq<int>|
                Self::admissible_starts(nums@, m as int, k as int, starts)
                    ==> #[trigger] Self::chosen_sum(nums@, m as int, starts) <= result as int,
    {
        let n = nums.len();
        let window_count = n - m + 1;

        let mut window_sums: Vec<i128> = Vec::new();
        let mut start: usize = 0;
        while start < window_count {
            let mut current: i128 = 0;
            let mut i: usize = 0;
            while i < m {
                current = current + nums[start + i] as i128;
                i = i + 1;
            }
            window_sums.push(current);
            start = start + 1;
        }

        let mut i: usize = 0;
        let mut prev: Vec<i128> = Vec::new();
        while i <= n {
            prev.push(0);
            i = i + 1;
        }

        let mut taken: usize = 1;
        while taken <= k {
            let mut curr: Vec<i128> = Vec::new();
            i = 0;
            while i <= n {
                curr.push(-1);
                i = i + 1;
            }
            let mut idx: usize = n;
            while idx > 0 {
                let pos = idx - 1;
                let skip = curr[pos + 1];
                let take: i128;
                if m <= n - pos {
                    let tail = prev[pos + m];
                    if tail < 0 || pos >= window_count {
                        take = -1;
                    } else {
                        take = window_sums[pos] + tail;
                    }
                } else {
                    take = -1;
                }
                let best = if skip >= take { skip } else { take };
                curr.set(pos, best);
                idx = pos;
            }
            prev = curr;
            taken = taken + 1;
        }

        let answer = prev[0];
        answer
    }
}

}
