use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn pow2(k: int) -> int
        decreases k,
    {
        if k <= 0 { 1 } else { 2 * Self::pow2(k - 1) }
    }

    pub open spec fn round_once(s: Seq<i32>) -> Seq<i32> {
        Seq::new(
            s.len() / 2,
            |i: int| {
                if i % 2 == 0 {
                    if s[2 * i] < s[2 * i + 1] { s[2 * i] } else { s[2 * i + 1] }
                } else {
                    if s[2 * i] > s[2 * i + 1] { s[2 * i] } else { s[2 * i + 1] }
                }
            },
        )
    }

    pub open spec fn game_after_steps(s: Seq<i32>, steps: int) -> Seq<i32>
        decreases steps,
    {
        if steps <= 0 || s.len() <= 1 {
            s
        } else {
            Self::game_after_steps(Self::round_once(s), steps - 1)
        }
    }

    pub open spec fn game_result(s: Seq<i32>) -> i32 {
        Self::game_after_steps(s, 10)[0]
    }

    pub fn min_max_game(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 1024,
            exists |k: int| 0 <= k <= 10 && nums.len() == Self::pow2(k),
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000_000,
        ensures
            exists |k: int| 0 <= k <= 10 && nums.len() == Self::pow2(k)
                && Self::game_after_steps(nums@, k) == seq![result],
    {
        let mut nums = nums;
        let ghost orig = nums@;
        let ghost k0 = choose |k: int| 0 <= k <= 10 && nums.len() == Self::pow2(k);
        let ghost mut cur = nums@;
        let ghost mut rem: int = k0;
        let mut n: usize = nums.len();

        while n > 1
            invariant
                1 <= n <= nums.len(),
                1 <= nums.len() <= 1024,
                n == cur.len(),
                0 <= rem <= k0 <= 10,
                n == Self::pow2(rem),
                Self::game_after_steps(cur, rem) == Self::game_after_steps(orig, k0),
                forall |i: int| 0 <= i < n ==> #[trigger] nums[i] == cur[i],
                forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000_000,
                forall |i: int| 0 <= i < n ==> 1 <= #[trigger] nums[i] <= 1_000_000_000,
            decreases n,
        {
            let ghost prev = cur;
            let mut i: usize = 0;
            while i < n / 2
                invariant
                    1 < n <= nums.len(),
                    n == prev.len(),
                    0 <= i <= n / 2,
                    1 <= nums.len() <= 1024,
                    forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 1_000_000_000,
                    forall |k: int| 0 <= k < i ==> nums[k] == Self::round_once(prev)[k],
                    forall |k: int| 2 * i <= k < n ==> nums[k] == prev[k],
                decreases n / 2 - i,
            {
                let old_i = i;
                let left = nums[2 * i];
                let right = nums[2 * i + 1];
                let val = if i % 2 == 0 {
                    if left < right { left } else { right }
                } else {
                    if left > right { left } else { right }
                };
                nums.set(i, val);
                i = i + 1;
                proof {
                    assert(left == prev[(2 * old_i) as int]);
                    assert(right == prev[(2 * old_i + 1) as int]);
                    assert(val == Self::round_once(prev)[old_i as int]);
                    assert(nums[old_i as int] == val);

                    assert forall |k: int| 0 <= k < i implies nums[k] == Self::round_once(prev)[k] by {
                        if k < old_i as int {
                        } else {
                            assert(k == old_i as int);
                        }
                    };

                    assert forall |k: int| 2 * i <= k < n implies nums[k] == prev[k] by {
                    };
                }
            }
            proof {
                assert(i == n / 2);
                assert(cur == prev);
                assert forall |k: int| 0 <= k < n / 2 implies nums[k] == Self::round_once(prev)[k] by {
                };
            }
            proof {
                cur = Self::round_once(prev);
                assert(rem > 0);
                rem = rem - 1;
                assert(Self::game_after_steps(prev, rem + 1) == Self::game_after_steps(orig, k0));
                assert(Self::game_after_steps(cur, rem) == Self::game_after_steps(orig, k0));
            }
            n = n / 2;
        }

        proof {
            assert(n == Self::pow2(rem));
            assert(rem == 0);
            assert(Self::game_after_steps(cur, 0) == Self::game_after_steps(orig, k0));
            assert(cur == Self::game_after_steps(orig, k0));
            assert(cur == Self::game_after_steps(orig, k0));
            assert(nums[0] == cur[0]);
            assert(cur.len() == 1);
            assert(cur == seq![nums[0]]);
        }

        nums[0]
    }
}

}
