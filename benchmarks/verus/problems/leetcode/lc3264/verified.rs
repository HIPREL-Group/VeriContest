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

    pub open spec fn pow5(n: int) -> int
        decreases n,
    {
        if n <= 0 {
            1
        } else {
            5 * Self::pow5(n - 1)
        }
    }

    proof fn lemma_to_int_update(s: Seq<i32>, idx: int, val: i32)
        requires
            0 <= idx < s.len(),
        ensures
            Self::to_int_seq(s.update(idx, val)) == Self::to_int_seq(s).update(idx, val as int),
    {
        assert(Self::to_int_seq(s.update(idx, val)).len() == s.len());
        assert(Self::to_int_seq(s).update(idx, val as int).len() == s.len());
        assert forall |j: int| 0 <= j < s.len() implies #[trigger] Self::to_int_seq(s.update(idx, val))[j] == Self::to_int_seq(s).update(idx, val as int)[j] by {
            if j == idx {
                assert(Self::to_int_seq(s.update(idx, val))[j] == val as int);
            } else {
                assert(s.update(idx, val)[j] == s[j]);
                assert(Self::to_int_seq(s.update(idx, val))[j] == s[j] as int);
            }
        };
    }

    proof fn lemma_min_index_prefix_bounds(s: Seq<int>, end: int)
        requires
            1 <= end <= s.len(),
        ensures
            0 <= Self::min_index_prefix(s, end) < end,
        decreases end,
    {
        if end <= 1 {
        } else {
            Self::lemma_min_index_prefix_bounds(s, end - 1);
            let j = Self::min_index_prefix(s, end - 1);
            assert(0 <= j < end - 1);
            if s[end - 1] < s[j] {
            } else {
                assert(j < end);
            }
        }
    }

    proof fn lemma_pow5_pos(n: int)
        requires
            0 <= n,
        ensures
            1 <= Self::pow5(n),
        decreases n,
    {
        if n <= 0 {
        } else {
            Self::lemma_pow5_pos(n - 1);
        }
    }

    proof fn lemma_pow5_le_9765625(n: int)
        requires
            0 <= n <= 10,
        ensures
            Self::pow5(n) <= 9_765_625,
    {
        if n == 0 {
            reveal_with_fuel(Solution::pow5, 1);
        } else if n == 1 {
            reveal_with_fuel(Solution::pow5, 2);
        } else if n == 2 {
            reveal_with_fuel(Solution::pow5, 3);
        } else if n == 3 {
            reveal_with_fuel(Solution::pow5, 4);
        } else if n == 4 {
            reveal_with_fuel(Solution::pow5, 5);
        } else if n == 5 {
            reveal_with_fuel(Solution::pow5, 6);
        } else if n == 6 {
            reveal_with_fuel(Solution::pow5, 7);
        } else if n == 7 {
            reveal_with_fuel(Solution::pow5, 8);
        } else if n == 8 {
            reveal_with_fuel(Solution::pow5, 9);
        } else if n == 9 {
            reveal_with_fuel(Solution::pow5, 10);
        } else {
            assert(n == 10);
            reveal_with_fuel(Solution::pow5, 11);
        }
    }

    proof fn lemma_mul_le_five(x: int, m: int)
        requires
            0 <= x,
            1 <= m <= 5,
        ensures
            x * m <= x * 5,
    {
        if m == 1 {
        } else if m == 2 {
        } else if m == 3 {
        } else if m == 4 {
        } else {
            assert(m == 5);
        }
    }

    proof fn lemma_mul_ge_one(x: int, m: int)
        requires
            1 <= x,
            1 <= m <= 5,
        ensures
            1 <= x * m,
    {
        if m == 1 {
        } else if m == 2 {
        } else if m == 3 {
        } else if m == 4 {
        } else {
            assert(m == 5);
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
        let mut nums = nums;
        let n = nums.len();
        let ghost init = Self::to_int_seq(nums@);
        let mut step: i32 = 0;
        while step < k
            invariant
                n == nums.len(),
                1 <= n <= 100,
                1 <= k <= 10,
                1 <= multiplier <= 5,
                0 <= step <= k,
                Self::to_int_seq(nums@) == Self::after_k(init, step as int, multiplier as int),
                forall |i: int| 0 <= i < nums.len() ==> {
                    &&& 1 <= #[trigger] nums[i] as int
                    &&& nums[i] as int <= 100 * Self::pow5(step as int)
                },
            decreases (k - step) as int,
        {
            let ghost before = nums@;
            let ghost before_int = Self::to_int_seq(before);

            let mut min_idx: usize = 0;
            let mut j: usize = 1;
            while j < n
                invariant
                    n == nums.len(),
                    nums@ == before,
                    before_int == Self::to_int_seq(before),
                    1 <= n <= 100,
                    1 <= k <= 10,
                    1 <= multiplier <= 5,
                    0 <= step < k,
                    1 <= j <= n,
                    0 <= min_idx < j,
                    min_idx as int == Self::min_index_prefix(before_int, j as int),
                decreases n - j,
            {
                let ghost old_idx = min_idx as int;
                if nums[j] < nums[min_idx] {
                    min_idx = j;
                    proof {
                        assert(before_int[j as int] == nums[j as int] as int);
                        assert(before_int[old_idx] == nums[old_idx] as int);
                        assert(before_int[j as int] < before_int[old_idx]);
                        assert(Self::min_index_prefix(before_int, (j + 1) as int) == j as int);
                    }
                } else {
                    proof {
                        assert(before_int[j as int] == nums[j as int] as int);
                        assert(before_int[old_idx] == nums[old_idx] as int);
                        assert(before_int[j as int] >= before_int[old_idx]);
                        assert(Self::min_index_prefix(before_int, (j + 1) as int) == old_idx);
                    }
                }
                j = j + 1;
                proof {
                    assert(min_idx as int == Self::min_index_prefix(before_int, j as int));
                }
            }

            proof {
                assert(j == n);
                assert(min_idx as int == Self::min_index_prefix(before_int, n as int));
                Self::lemma_min_index_prefix_bounds(before_int, n as int);
                assert(0 <= min_idx < n);
            }

            let old_val: i32 = nums[min_idx];
            proof {
                assert(1 <= old_val as int <= 100 * Self::pow5(step as int));
                assert(step + 1 <= k);
                assert((step + 1) as int <= 10);
                Self::lemma_mul_le_five(old_val as int, multiplier as int);
                assert(old_val as int * multiplier as int <= old_val as int * 5);
                assert(old_val as int * 5 <= 100 * Self::pow5(step as int) * 5);
                assert(100 * Self::pow5((step + 1) as int) == 100 * (5 * Self::pow5(step as int)));
                assert(old_val as int * multiplier as int <= 100 * Self::pow5((step + 1) as int));
                Self::lemma_pow5_le_9765625((step + 1) as int);
                assert(100 * Self::pow5((step + 1) as int) <= 976_562_500);
                assert(old_val as int * multiplier as int <= 2_147_483_647);
                Self::lemma_mul_ge_one(old_val as int, multiplier as int);
            }
            let new_val: i32 = old_val * multiplier;
            nums.set(min_idx, new_val);

            proof {
                assert(before_int[min_idx as int] == old_val as int);
                assert(new_val as int == old_val as int * multiplier as int);
                Self::lemma_to_int_update(before, min_idx as int, new_val);
                assert(Self::to_int_seq(nums@) == before_int.update(min_idx as int, new_val as int));
                assert(before_int.update(min_idx as int, new_val as int)
                    == before_int.update(min_idx as int, before_int[min_idx as int] * multiplier as int));
                assert(Self::apply_once(before_int, multiplier as int)
                    == before_int.update(Self::min_index_prefix(before_int, before_int.len() as int),
                        before_int[Self::min_index_prefix(before_int, before_int.len() as int)] * multiplier as int));
                assert(min_idx as int == Self::min_index_prefix(before_int, before_int.len() as int));
                assert(Self::to_int_seq(nums@) == Self::apply_once(before_int, multiplier as int));
                assert(Self::after_k(init, (step + 1) as int, multiplier as int)
                    == Self::apply_once(Self::after_k(init, step as int, multiplier as int), multiplier as int));
                assert(Self::after_k(init, step as int, multiplier as int) == before_int);
                assert(Self::to_int_seq(nums@) == Self::after_k(init, (step + 1) as int, multiplier as int));

                assert forall |i: int| 0 <= i < nums.len() implies {
                    &&& 1 <= #[trigger] nums[i] as int
                    &&& nums[i] as int <= 100 * Self::pow5((step + 1) as int)
                } by {
                    if i == min_idx as int {
                        assert(nums[i] == new_val);
                        assert(1 <= new_val as int);
                        assert(new_val as int <= 100 * Self::pow5((step + 1) as int));
                    } else {
                        assert(nums[i] == before[i]);
                        assert(1 <= before[i] as int <= 100 * Self::pow5(step as int));
                        Self::lemma_pow5_pos(step as int);
                        assert(100 * Self::pow5(step as int) <= 100 * Self::pow5((step + 1) as int));
                    }
                };
            }

            step = step + 1;
        }

        nums
    }
}

}
