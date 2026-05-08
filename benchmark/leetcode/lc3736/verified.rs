use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn seq_max(s: Seq<i32>, end: int) -> int
        decreases end,
    {
        if end <= 1 {
            if end <= 0 { 0 } else { s[0] as int }
        } else {
            let prev = Self::seq_max(s, end - 1);
            let cur = s[end - 1] as int;
            if prev >= cur { prev } else { cur }
        }
    }

    pub open spec fn seq_moves_to_target(s: Seq<i32>, target: int, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::seq_moves_to_target(s, target, end - 1) + (target - s[end - 1] as int)
        }
    }

    pub open spec fn min_moves_spec(nums: Seq<i32>) -> int {
        let n = nums.len() as int;
        Self::seq_moves_to_target(nums, Self::seq_max(nums, n), n)
    }

    proof fn lemma_seq_max_unfold(s: Seq<i32>, end: int)
        requires
            1 <= end < s.len(),
        ensures
            Self::seq_max(s, end + 1) == (if Self::seq_max(s, end) >= s[end] as int {
                Self::seq_max(s, end)
            } else {
                s[end] as int
            }),
        decreases end,
    {
        reveal_with_fuel(Solution::seq_max, 3);
    }

    proof fn lemma_seq_moves_unfold(s: Seq<i32>, target: int, end: int)
        requires
            0 <= end < s.len(),
        ensures
            Self::seq_moves_to_target(s, target, end + 1)
                == Self::seq_moves_to_target(s, target, end) + (target - s[end] as int),
        decreases end,
    {
        reveal_with_fuel(Solution::seq_moves_to_target, 3);
    }

    proof fn lemma_seq_max_ge_index(s: Seq<i32>, end: int, j: int)
        requires
            1 <= end <= s.len(),
            0 <= j < end,
        ensures
            s[j] as int <= Self::seq_max(s, end),
        decreases end,
    {
        if end <= 1 {
            reveal_with_fuel(Solution::seq_max, 2);
        } else {
            Self::lemma_seq_max_unfold(s, end - 1);
            if j < end - 1 {
                Self::lemma_seq_max_ge_index(s, end - 1, j);
                if Self::seq_max(s, end - 1) >= s[end - 1] as int {
                    assert(Self::seq_max(s, end) == Self::seq_max(s, end - 1));
                } else {
                    assert(Self::seq_max(s, end) == s[end - 1] as int);
                    assert(s[j] as int <= Self::seq_max(s, end - 1));
                    assert(Self::seq_max(s, end - 1) < s[end - 1] as int);
                    assert((s[j] as int) < (s[end - 1] as int));
                }
            } else {
                assert(j == end - 1);
                if Self::seq_max(s, end - 1) >= s[end - 1] as int {
                    assert(Self::seq_max(s, end) == Self::seq_max(s, end - 1));
                    assert(s[end - 1] as int <= Self::seq_max(s, end - 1));
                } else {
                    assert(Self::seq_max(s, end) == s[end - 1] as int);
                }
            }
        }
    }

    pub fn min_moves(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
        ensures
            result as int == Self::min_moves_spec(nums@),
    {
        let n = nums.len();
        let mut max_val = nums[0];
        let mut i = 1usize;

        proof {
            reveal_with_fuel(Solution::seq_max, 2);
            assert(Self::seq_max(nums@, 1) == nums[0] as int);
        }

        while i < n
            invariant
                1 <= n <= 100,
                n == nums.len(),
                1 <= i <= n,
                forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 100,
                max_val as int == Self::seq_max(nums@, i as int),
                1 <= max_val <= 100,
            decreases n - i,
        {
            let cur = nums[i];
            let old_max = max_val;
            if cur > old_max {
                max_val = cur;
            } else {
                max_val = old_max;
            }
            proof {
                Self::lemma_seq_max_unfold(nums@, i as int);
                if old_max as int >= cur as int {
                    assert(Self::seq_max(nums@, i as int + 1) == Self::seq_max(nums@, i as int));
                } else {
                    assert(Self::seq_max(nums@, i as int + 1) == cur as int);
                }
            }
            i = i + 1;
        }

        proof {
            assert(i == n);
        }

        let mut ans: i64 = 0;
        let mut j = 0usize;
        while j < n
            invariant
                1 <= n <= 100,
                n == nums.len(),
                forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 100,
                max_val as int == Self::seq_max(nums@, n as int),
                1 <= max_val <= 100,
                0 <= j <= n,
                ans as int == Self::seq_moves_to_target(nums@, max_val as int, j as int),
                0 <= ans as int <= 100 * (j as int),
            decreases n - j,
        {
            proof {
                Self::lemma_seq_max_ge_index(nums@, n as int, j as int);
                assert(nums@[j as int] as int <= max_val as int);
                Self::lemma_seq_moves_unfold(nums@, max_val as int, j as int);
            }
            let delta = max_val - nums[j];
            proof {
                assert(delta as int == max_val as int - nums@[j as int] as int);
                assert(1 <= nums@[j as int] as int <= 100);
                assert(0 <= max_val as int - nums@[j as int] as int);
                assert(max_val as int - nums@[j as int] as int <= max_val as int);
                assert(max_val as int <= 100);
                assert(0 <= delta as int <= 100);
                assert(ans as int + delta as int <= 100 * ((j as int) + 1));
            }
            ans = ans + delta as i64;
            j = j + 1;
        }

        proof {
            assert(j == n);
            assert(ans as int == Self::seq_moves_to_target(nums@, max_val as int, n as int));
            assert(max_val as int == Self::seq_max(nums@, n as int));
            assert(Self::min_moves_spec(nums@) == Self::seq_moves_to_target(nums@, max_val as int, n as int));
            assert(0 <= ans as int <= 10000);
            assert(-2147483648 <= ans as int <= 2147483647);
        }

        ans as i32
    }
}

}
