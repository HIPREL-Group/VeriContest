use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn freq_prefix(nums: Seq<i32>, v: int, end: int) -> int
        recommends
            0 <= end <= nums.len(),
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::freq_prefix(nums, v, end - 1) + if (nums[end - 1] as int) == v {
                1int
            } else {
                0int
            }
        }
    }

    pub open spec fn freq_at(nums: Seq<i32>, v: int) -> int {
        Self::freq_prefix(nums, v, nums.len() as int)
    }

    pub open spec fn canonical_counts(nums: Seq<i32>) -> Seq<u64> {
        Seq::new(100_001, |i: int|
            if i == 0 {
                0u64
            } else {
                Self::freq_at(nums, i) as u64
            }
        )
    }

    pub open spec fn dp_best(cnt: Seq<u64>, i: int) -> int
        recommends
            0 <= i <= 100_000,
            cnt.len() == 100_001,
            forall |k: int| 0 <= k < cnt.len() ==> #[trigger] cnt[k] <= 100_000,
        decreases i,
    {
        if i <= 0 {
            0
        } else {
            let prev2 = if i >= 2 {
                Self::dp_best(cnt, i - 2)
            } else {
                0
            };
            let take = prev2 + i * (cnt[i] as int);
            let skip = Self::dp_best(cnt, i - 1);
            if take > skip {
                take
            } else {
                skip
            }
        }
    }

    proof fn lemma_freq_prefix_split(nums: Seq<i32>, v: int, end: int)
        requires
            0 < end <= nums.len(),
        ensures
            Self::freq_prefix(nums, v, end) == Self::freq_prefix(nums, v, end - 1) + if (nums[end - 1] as int) == v {
                1int
            } else {
                0int
            },
    {
    }

    proof fn lemma_freq_prefix_v_zero(nums: Seq<i32>, end: int)
        requires
            0 <= end <= nums.len(),
            forall |t: int| 0 <= t < end ==> 1 <= #[trigger] nums[t],
        ensures
            Self::freq_prefix(nums, 0, end) == 0,
        decreases end,
    {
        if end <= 0 {
        } else {
            Self::lemma_freq_prefix_v_zero(nums, end - 1);
            assert((nums[end - 1] as int) != 0);
        }
    }

    proof fn lemma_freq_prefix_le_len(nums: Seq<i32>, v: int, end: int)
        requires
            0 <= end <= nums.len(),
        ensures
            Self::freq_prefix(nums, v, end) <= end,
        decreases end,
    {
        if end <= 0 {
        } else {
            Self::lemma_freq_prefix_le_len(nums, v, end - 1);
            reveal_with_fuel(Solution::freq_prefix, 2);
        }
    }

    proof fn lemma_cnt_eq_canonical_after_fill(
        nums: Seq<i32>,
        cnt: Seq<u64>,
    )
        requires
            nums.len() <= 100_000,
            1 <= nums.len(),
            forall |t: int| 0 <= t < nums.len() ==> 1 <= #[trigger] nums[t] <= 100_000,
            cnt.len() == 100_001,
            forall |idx: int|
                0 <= idx < 100_001 ==> #[trigger] cnt[idx] as int == Self::freq_prefix(nums, idx, nums.len() as int),
        ensures
            cnt == Self::canonical_counts(nums),
    {
        Self::lemma_freq_prefix_v_zero(nums, nums.len() as int);
        assert forall |idx: int|
            0 <= idx < 100_001 implies cnt[idx] == Self::canonical_counts(nums)[idx] by {
            if idx == 0 {
                assert(Self::freq_prefix(nums, 0, nums.len() as int) == 0);
                assert(Self::canonical_counts(nums)[0] == 0u64);
            } else {
                assert(cnt[idx] as int == Self::freq_prefix(nums, idx, nums.len() as int));
                assert(Self::freq_at(nums, idx) == Self::freq_prefix(nums, idx, nums.len() as int));
                assert(Self::canonical_counts(nums)[idx] == Self::freq_at(nums, idx) as u64);
            }
        }
        assert(cnt == Self::canonical_counts(nums));
    }

    proof fn lemma_dp_step(cnt: Seq<u64>, i: int)
        requires
            1 <= i <= 100_000,
            cnt.len() == 100_001,
            forall |k: int| 0 <= k < cnt.len() ==> #[trigger] cnt[k] <= 100_000,
        ensures
            Self::dp_best(cnt, i)
                == if Self::dp_best(cnt, i - 1)
                    > (if i >= 2 {
                        Self::dp_best(cnt, i - 2)
                    } else {
                        0
                    }) + i * (cnt[i] as int)
                {
                    Self::dp_best(cnt, i - 1)
                } else {
                    (if i >= 2 {
                        Self::dp_best(cnt, i - 2)
                    } else {
                        0
                    }) + i * (cnt[i] as int)
                },
    {
        reveal_with_fuel(Solution::dp_best, 4);
    }

    proof fn lemma_dp_best_nonnegative(cnt: Seq<u64>, i: int)
        requires
            0 <= i <= 100_000,
            cnt.len() == 100_001,
            forall |k: int| 0 <= k < cnt.len() ==> #[trigger] cnt[k] <= 100_000,
        ensures
            Self::dp_best(cnt, i) >= 0,
        decreases i,
    {
        if i <= 0 {
        } else {
            Self::lemma_dp_best_nonnegative(cnt, i - 1);
            if i >= 2 {
                Self::lemma_dp_best_nonnegative(cnt, i - 2);
            }
            reveal_with_fuel(Solution::dp_best, 4);
        }
    }

    proof fn lemma_dp_best_bound_crude(cnt: Seq<u64>, i: int)
        requires
            0 <= i <= 100_000,
            cnt.len() == 100_001,
            forall |k: int| 0 <= k < cnt.len() ==> #[trigger] cnt[k] <= 100_000,
        ensures
            Self::dp_best(cnt, i) <= i * 100_000 * 100_000,
        decreases i,
    {
        let m: int = 10_000_000_000int;
        if i <= 0 {
        } else {
            Self::lemma_dp_best_bound_crude(cnt, i - 1);
            if i >= 2 {
                Self::lemma_dp_best_bound_crude(cnt, i - 2);
            }
            reveal_with_fuel(Solution::dp_best, 4);
            assert(100_000 * 100_000 == m);
            assert(0 <= i && i < cnt.len());
            assert((cnt[i] as int) <= 100_000);
            assert(0 <= (cnt[i] as int));
            assert(i * (cnt[i] as int) <= 100_000 * 100_000) by (nonlinear_arith)
                requires
                    0 <= i && i <= 100_000,
                    0 <= (cnt[i] as int) && (cnt[i] as int) <= 100_000,
            ;
            assert(i * (cnt[i] as int) <= m);
            assert(m > 0);
            assert(i * m == (i - 1) * m + m) by (nonlinear_arith)
                requires
                    i >= 1,
            ;
            assert((i - 1) * m <= i * m);
            if i == 1 {
                assert(Self::dp_best(cnt, i - 1) == 0);
                assert((if i >= 2 {
                    Self::dp_best(cnt, i - 2)
                } else {
                    0
                }) + i * (cnt[i] as int) <= m);
                assert(Self::dp_best(cnt, i) <= m);
                assert(i * m == m);
            } else {
                assert(i >= 2);
                assert(Self::dp_best(cnt, i - 1) <= (i - 1) * m);
                assert(Self::dp_best(cnt, i - 2) <= (i - 2) * m);
                assert(
                    Self::dp_best(cnt, i - 2) + i * (cnt[i] as int) <= (i - 2) * m + m
                ) by (nonlinear_arith)
                    requires
                        Self::dp_best(cnt, i - 2) <= (i - 2) * m,
                        i * (cnt[i] as int) <= m,
                ;
                assert((i - 2) * m + m == (i - 1) * m) by (nonlinear_arith)
                    requires
                        i >= 2,
                ;
                assert(Self::dp_best(cnt, i - 1) <= (i - 1) * m);
                assert((i - 1) * m <= i * m);
            }
        }
    }

    proof fn lemma_freq_inv_after_step(
        nums: Seq<i32>,
        old_cnt: Seq<u64>,
        new_cnt: Seq<u64>,
        j: int,
        v: int,
    )
        requires
            0 <= j < nums.len(),
            nums.len() <= 100_000,
            forall |t: int| 0 <= t < nums.len() ==> 1 <= #[trigger] nums[t] <= 100_000,
            1 <= v && v <= 100_000,
            (nums[j] as int) == v,
            old_cnt.len() == 100_001,
            new_cnt.len() == 100_001,
            forall |idx: int|
                0 <= idx < 100_001 ==> #[trigger] old_cnt[idx] as int == Self::freq_prefix(nums, idx, j),
            forall |idx: int|
                0 <= idx < 100_001 && idx != v ==> #[trigger] new_cnt[idx] == old_cnt[idx],
            new_cnt[v as int] == old_cnt[v as int] + 1,
        ensures
            forall |idx: int|
                0 <= idx < 100_001 ==> #[trigger] new_cnt[idx] as int == Self::freq_prefix(nums, idx, j + 1),
    {
        assert forall |idx: int|
            0 <= idx < 100_001 implies new_cnt[idx] as int == Self::freq_prefix(nums, idx, j + 1) by {
            Self::lemma_freq_prefix_split(nums, idx, j + 1);
            if idx == v {
                assert(Self::freq_prefix(nums, idx, j + 1) == Self::freq_prefix(nums, idx, j) + 1);
                assert(new_cnt[idx] as int == old_cnt[idx] as int + 1);
            } else {
                assert((nums[j] as int) != idx);
                assert(Self::freq_prefix(nums, idx, j + 1) == Self::freq_prefix(nums, idx, j));
                assert(new_cnt[idx] as int == old_cnt[idx] as int);
            }
        }
    }

    pub fn max_boredom_points(nums: Vec<i32>) -> (result: i64)
        requires
            1 <= nums.len() <= 100_000,
            forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 100_000,
        ensures
            result as int == Self::dp_best(Self::canonical_counts(nums@), 100_000),
    {
        let mut cnt: Vec<u64> = Vec::new();
        let mut t: usize = 0;
        while t < 100_001
            invariant
                t <= 100_001,
                cnt.len() == t,
                forall |k: int| 0 <= k < cnt.len() as int ==> #[trigger] cnt[k] == 0,
            decreases 100_001 - t,
        {
            cnt.push(0);
            t = t + 1;
        }
        let mut j: usize = 0;
        while j < nums.len()
            invariant
                nums.len() <= 100_000,
                cnt.len() == 100_001,
                j <= nums.len(),
                forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums@[k] <= 100_000,
                forall |idx: int|
                    0 <= idx < 100_001 ==> #[trigger] cnt@[idx] as int
                        == Self::freq_prefix(nums@, idx, j as int),
            decreases nums.len() - j,
        {
            let v = nums[j] as usize;
            let oldc = cnt[v];
            let ghost cnt_before = cnt@;
            proof {
                assert(1 <= nums@[j as int] <= 100_000);
                assert(1 <= v && v <= 100_000);
                assert((nums@[j as int] as int) == v as int);
                assert(oldc as int == Self::freq_prefix(nums@, v as int, j as int));
                Self::lemma_freq_prefix_le_len(nums@, v as int, j as int);
                assert(oldc as int <= j as int);
                assert(j < nums.len());
                assert(oldc <= nums.len() as u64);
                assert(oldc <= 100_000);
            }
            cnt.set(v, oldc + 1);
            proof {
                Self::lemma_freq_inv_after_step(nums@, cnt_before, cnt@, j as int, v as int);
            }
            j = j + 1;
        }
        proof {
            Self::lemma_cnt_eq_canonical_after_fill(nums@, cnt@);
            assert(cnt@ == Self::canonical_counts(nums@));
            assert forall |k: int|
                0 <= k < cnt.len() implies #[trigger] cnt@[k] <= 100_000 by {
                Self::lemma_freq_prefix_le_len(nums@, k, nums.len() as int);
                assert(cnt@[k] as int == Self::freq_prefix(nums@, k, nums.len() as int));
            }
        }
        let ghost nums_seq = nums@;
        let ghost cnt_seq = cnt@;
        let mut dp_i_minus_2: i64 = 0;
        let mut dp_i_minus_1: i64 = 0;
        let mut i_val: usize = 1;
        while i_val <= 100_000
            invariant
                cnt.len() == 100_001,
                nums@ == nums_seq,
                cnt@ == cnt_seq,
                cnt_seq == Self::canonical_counts(nums_seq),
                1 <= i_val && i_val <= 100_001,
                forall |k: int| 0 <= k < cnt.len() ==> #[trigger] cnt[k] <= 100_000,
                dp_i_minus_2 as int == Self::dp_best(
                    cnt_seq,
                    if (i_val as int) <= 2 {
                        0
                    } else {
                        (i_val as int) - 2
                    },
                ),
                dp_i_minus_1 as int == Self::dp_best(cnt_seq, (i_val as int) - 1),
                dp_i_minus_2 >= 0,
                dp_i_minus_1 >= 0,
                dp_i_minus_2 as int
                    <= if (i_val as int) <= 2 {
                        0
                    } else {
                        ((i_val as int) - 2) * 100_000 * 100_000
                    },
                dp_i_minus_1 as int <= ((i_val as int) - 1) * 100_000 * 100_000,
            decreases 100_001 - i_val,
        {
            let vi = i_val as i64;
            proof {
                Self::lemma_dp_best_nonnegative(
                    cnt_seq,
                    if (i_val as int) <= 2 {
                        0
                    } else {
                        (i_val as int) - 2
                    },
                );
                Self::lemma_dp_best_nonnegative(cnt_seq, (i_val as int) - 1);
                Self::lemma_dp_best_bound_crude(
                    cnt_seq,
                    if (i_val as int) <= 2 {
                        0
                    } else {
                        (i_val as int) - 2
                    },
                );
                Self::lemma_dp_best_bound_crude(cnt_seq, (i_val as int) - 1);
                assert(0 <= (i_val as int) && (i_val as int) <= 100_000);
                assert(
                    0 <= (cnt_seq[i_val as int] as int) && (cnt_seq[i_val as int] as int) <= 100_000
                );
                assert(
                    (i_val as int) * (cnt_seq[i_val as int] as int) <= 10_000_000_000int
                ) by (nonlinear_arith)
                    requires
                        0 <= (i_val as int) && (i_val as int) <= 100_000,
                        0 <= (cnt_seq[i_val as int] as int) && (cnt_seq[i_val as int] as int) <= 100_000,
                ;
                assert((vi as int) * (cnt_seq[i_val as int] as int) <= 10_000_000_000int);
            }
            let take = dp_i_minus_2 + vi * (cnt[i_val] as i64);
            let cur = if take > dp_i_minus_1 {
                take
            } else {
                dp_i_minus_1
            };
            proof {
                Self::lemma_dp_step(cnt_seq, i_val as int);
                assert(take as int == Self::dp_best(cnt_seq, if (i_val as int) <= 2 {
                    0
                } else {
                    (i_val as int) - 2
                }) + (i_val as int) * (cnt_seq[i_val as int] as int));
                assert(dp_i_minus_2 as int == Self::dp_best(cnt_seq, if (i_val as int) <= 2 {
                    0
                } else {
                    (i_val as int) - 2
                }));
                assert((vi * (cnt@[i_val as int] as i64)) as int == (i_val as int) * (cnt_seq[i_val as int] as int));
                assert(take as int == (if (i_val as int) >= 2 {
                    Self::dp_best(cnt_seq, (i_val as int) - 2)
                } else {
                    0
                }) + (i_val as int) * (cnt_seq[i_val as int] as int));
                assert(cur as int == Self::dp_best(cnt_seq, i_val as int));
                Self::lemma_dp_best_nonnegative(cnt_seq, i_val as int);
                Self::lemma_dp_best_bound_crude(cnt_seq, i_val as int);
            }
            dp_i_minus_2 = dp_i_minus_1;
            dp_i_minus_1 = cur;
            i_val = i_val + 1;
            proof {
                assert(dp_i_minus_2 as int == Self::dp_best(cnt_seq, (i_val as int) - 2));
                assert(dp_i_minus_1 as int == Self::dp_best(cnt_seq, (i_val as int) - 1));
            }
        }
        proof {
            assert(i_val == 100_001);
            assert(dp_i_minus_1 as int == Self::dp_best(cnt_seq, 100_000));
            assert(Self::dp_best(cnt_seq, 100_000) == Self::dp_best(Self::canonical_counts(nums_seq), 100_000));
        }
        dp_i_minus_1
    }
}

}
