use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn div_contrib(nums: Seq<i32>, d: int, idx: nat) -> nat {
        if (nums[idx as int] as int) % d == 0 { 1nat } else { 0nat }
    }

    pub open spec fn div_score_prefix(nums: Seq<i32>, d: int, k: nat) -> nat
        decreases k,
    {
        if k == 0 {
            0
        } else {
            Self::div_score_prefix(nums, d, (k - 1) as nat) + Self::div_contrib(nums, d, (k - 1) as nat)
        }
    }

    pub open spec fn div_score(nums: Seq<i32>, d: int) -> nat {
        Self::div_score_prefix(nums, d, nums.len() as nat)
    }

    pub open spec fn best_divisor_prefix(nums: Seq<i32>, divisors: Seq<i32>, k: nat) -> int
        decreases k,
    {
        if k == 0 {
            0
        } else if k == 1 {
            divisors[0] as int
        } else {
            let prev = Self::best_divisor_prefix(nums, divisors, (k - 1) as nat);
            let cur = divisors[k as int - 1] as int;
            let s_prev = Self::div_score(nums, prev);
            let s_cur = Self::div_score(nums, cur);
            if s_cur > s_prev || (s_cur == s_prev && cur < prev) {
                cur
            } else {
                prev
            }
        }
    }

    fn score(nums: &Vec<i32>, d: i32) -> (result: i32)
        requires
            1 <= nums.len() <= 1000,
            d > 0,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000_000,
        ensures
            result as nat == Self::div_score(nums@, d as int),
            0 <= result <= nums.len(),
    {
        let mut i: usize = 0;
        let mut count: i32 = 0;
        while i < nums.len()
            invariant
                0 <= i <= nums.len(),
                1 <= nums.len() <= 1000,
                0 <= count <= i,
                d > 0,
                forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 1_000_000_000,
                count as nat == Self::div_score_prefix(nums@, d as int, i as nat),
            decreases nums.len() - i,
        {
            let old_i = i;
            let old_count = count;
            if nums[i] % d == 0 {
                count = count + 1;
            }
            i = i + 1;
            proof {
                assert(Self::div_score_prefix(nums@, d as int, i as nat)
                    == Self::div_score_prefix(nums@, d as int, old_i as nat)
                        + Self::div_contrib(nums@, d as int, old_i as nat));
                if (nums@[old_i as int] as int) % (d as int) == 0 {
                    assert(Self::div_contrib(nums@, d as int, old_i as nat) == 1nat);
                    assert(count == old_count + 1);
                } else {
                    assert(Self::div_contrib(nums@, d as int, old_i as nat) == 0nat);
                    assert(count == old_count);
                }
            }
        }
        count
    }

    pub fn max_div_score(nums: Vec<i32>, divisors: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 1000,
            1 <= divisors.len() <= 1000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000_000,
            forall |i: int| 0 <= i < divisors.len() ==> 1 <= #[trigger] divisors[i] <= 1_000_000_000,
        ensures
            result as int == Self::best_divisor_prefix(nums@, divisors@, divisors.len() as nat),
    {
        let mut best: i32 = divisors[0];
        let mut best_score: i32 = Self::score(&nums, best);

        let mut i: usize = 1;
        while i < divisors.len()
            invariant
                1 <= i <= divisors.len(),
                1 <= nums.len() <= 1000,
                1 <= divisors.len() <= 1000,
                forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 1_000_000_000,
                forall |k: int| 0 <= k < divisors.len() ==> 1 <= #[trigger] divisors[k] <= 1_000_000_000,
                1 <= best <= 1_000_000_000,
                0 <= best_score <= nums.len(),
                best as int == Self::best_divisor_prefix(nums@, divisors@, i as nat),
                best_score as nat == Self::div_score(nums@, best as int),
            decreases divisors.len() - i,
        {
            let cur = divisors[i];
            proof {
                assert(0 <= i < divisors.len());
                assert(1 <= cur <= 1_000_000_000);
            }
            let cur_score = Self::score(&nums, cur);
            if cur_score > best_score || (cur_score == best_score && cur < best) {
                best = cur;
                best_score = cur_score;
            }
            i = i + 1;
            proof {
                assert(Self::best_divisor_prefix(nums@, divisors@, i as nat)
                    == {
                        let prev = Self::best_divisor_prefix(nums@, divisors@, ((i - 1) as nat));
                        let now = divisors[(i - 1) as int] as int;
                        let s_prev = Self::div_score(nums@, prev);
                        let s_now = Self::div_score(nums@, now);
                        if s_now > s_prev || (s_now == s_prev && now < prev) {
                            now
                        } else {
                            prev
                        }
                    });
            }
        }

        best
    }
}

}
