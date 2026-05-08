use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn seq_sum(s: Seq<i32>, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::seq_sum(s, end - 1) + s[end - 1] as int
        }
    }

    pub open spec fn seq_min(s: Seq<i32>, end: int) -> int
        decreases end,
    {
        if end <= 1 {
            if end <= 0 { 0 } else { s[0] as int }
        } else {
            let prev = Self::seq_min(s, end - 1);
            let cur = s[end - 1] as int;
            if prev <= cur { prev } else { cur }
        }
    }

    pub open spec fn min_moves_spec(nums: Seq<i32>) -> int {
        let n = nums.len() as int;
        Self::seq_sum(nums, n) - n * Self::seq_min(nums, n)
    }

    proof fn lemma_seq_sum_unfold(s: Seq<i32>, end: int)
        requires 0 <= end <= s.len(),
        ensures
            Self::seq_sum(s, end + 1) == Self::seq_sum(s, end) + s[end] as int,
        decreases end,
    {
        reveal_with_fuel(Solution::seq_sum, 3);
    }

    proof fn lemma_seq_min_unfold(s: Seq<i32>, end: int)
        requires 1 <= end < s.len(),
        ensures
            Self::seq_min(s, end + 1) == (if Self::seq_min(s, end) <= s[end] as int
                { Self::seq_min(s, end) } else { s[end] as int }),
        decreases end,
    {
        reveal_with_fuel(Solution::seq_min, 3);
    }

    proof fn lemma_seq_min_single(s: Seq<i32>)
        requires 1 <= s.len(),
        ensures Self::seq_min(s, 1) == s[0] as int,
    {
        reveal_with_fuel(Solution::seq_min, 2);
    }

    pub fn min_moves(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 100_000,
            forall |i: int| 0 <= i < nums.len() ==>
                -1_000_000_000 <= #[trigger] nums[i] <= 1_000_000_000,
            Self::min_moves_spec(nums@) >= -2_147_483_648,
            Self::min_moves_spec(nums@) <= 2_147_483_647,
        ensures
            result as int == Self::min_moves_spec(nums@),
    {
        let n = nums.len();
        let mut min_val = nums[0];
        let mut sum = nums[0] as i64;
        let mut i = 1usize;

        proof {
            reveal_with_fuel(Solution::seq_sum, 2);
            reveal_with_fuel(Solution::seq_min, 2);
            assert(Self::seq_sum(nums@, 1) == nums[0] as int);
            assert(Self::seq_min(nums@, 1) == nums[0] as int);
        }

        while i < n
            invariant
                1 <= n <= 100_000,
                n == nums.len(),
                1 <= i <= n,
                forall |j: int| 0 <= j < nums.len() ==>
                    -1_000_000_000 <= #[trigger] nums[j] <= 1_000_000_000,
                min_val as int == Self::seq_min(nums@, i as int),
                sum as int == Self::seq_sum(nums@, i as int),
                -(i as int) * 1_000_000_000 <= sum as int <= (i as int) * 1_000_000_000,
                -102_000_000_000_000i64 <= sum <= 102_000_000_000_000i64,
            decreases n - i,
        {
            if nums[i] < min_val {
                min_val = nums[i];
            }
            proof {
                Self::lemma_seq_sum_unfold(nums@, i as int);
                Self::lemma_seq_min_unfold(nums@, i as int);
                assert(Self::seq_sum(nums@, i as int + 1) == Self::seq_sum(nums@, i as int) + nums@[i as int] as int);
                assert(-102_000_000_000_000 <= sum as int + nums@[i as int] as int <= 102_000_000_000_000);
            }
            sum = sum + nums[i] as i64;
            i = i + 1;
        }

        proof {
            assert(sum as int == Self::seq_sum(nums@, n as int));
            assert(min_val as int == Self::seq_min(nums@, n as int));
            assert(Self::min_moves_spec(nums@) == Self::seq_sum(nums@, n as int)
                - (n as int) * Self::seq_min(nums@, n as int));
            assert((sum - (n as i64) * (min_val as i64)) as int == Self::min_moves_spec(nums@));
            assert(-2_147_483_648 <= (sum - (n as i64) * (min_val as i64)) <= 2_147_483_647);
        }
        (sum - (n as i64) * (min_val as i64)) as i32
    }
}

}
