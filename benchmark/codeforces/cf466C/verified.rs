use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn prefix_sum(nums: Seq<i64>, end: int) -> int
        recommends
            0 <= end <= nums.len(),
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::prefix_sum(nums, end - 1) + nums[end - 1] as int
        }
    }

    pub open spec fn total_sum(nums: Seq<i64>) -> int {
        Self::prefix_sum(nums, nums.len() as int)
    }

    pub open spec fn valid_split_pair(nums: Seq<i64>, i: int, j: int) -> bool {
        &&& 0 <= i < j < nums.len() - 1
        &&& {
            let s1 = Self::prefix_sum(nums, i + 1);
            let s2 = Self::prefix_sum(nums, j + 1) - Self::prefix_sum(nums, i + 1);
            let s3 = Self::total_sum(nums) - Self::prefix_sum(nums, j + 1);
            s1 == s2 && s2 == s3
        }
    }

    pub open spec fn count_valid_first_cuts(nums: Seq<i64>, j: int, i_end: int) -> nat
        recommends
            -1 <= j < nums.len() - 1,
            0 <= i_end <= j,
        decreases i_end,
    {
        if i_end <= 0 {
            0
        } else {
            Self::count_valid_first_cuts(nums, j, i_end - 1) + if Self::valid_split_pair(nums, i_end - 1, j) {
                1nat
            } else {
                0nat
            }
        }
    }

    pub open spec fn count_valid_splits_upto(nums: Seq<i64>, j_end: int) -> nat
        recommends
            0 <= j_end <= nums.len() - 1,
        decreases j_end,
    {
        if j_end <= 0 {
            0
        } else {
            Self::count_valid_splits_upto(nums, j_end - 1)
                + Self::count_valid_first_cuts(nums, j_end - 1, j_end - 1)
        }
    }

    pub open spec fn count_valid_splits(nums: Seq<i64>) -> nat {
        if nums.len() < 3 {
            0
        } else {
            Self::count_valid_splits_upto(nums, nums.len() - 1)
        }
    }

    pub open spec fn count_target_prefixes(nums: Seq<i64>, target: int, end: int) -> nat
        recommends
            0 <= end <= nums.len() - 1,
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::count_target_prefixes(nums, target, end - 1) + if Self::prefix_sum(nums, end) == target {
                1nat
            } else {
                0nat
            }
        }
    }

    pub open spec fn count_prefix_split_pairs(nums: Seq<i64>, target: int, end: int) -> nat
        recommends
            0 <= end <= nums.len() - 1,
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::count_prefix_split_pairs(nums, target, end - 1) + if Self::prefix_sum(nums, end) == 2 * target {
                Self::count_target_prefixes(nums, target, end - 1)
            } else {
                0nat
            }
        }
    }

    proof fn lemma_prefix_sum_step(nums: Seq<i64>, i: int)
        requires
            0 <= i < nums.len(),
        ensures
            Self::prefix_sum(nums, i + 1) == Self::prefix_sum(nums, i) + nums[i] as int,
    {
    }

    proof fn lemma_prefix_targets_imply_valid_split_pair(nums: Seq<i64>, i: int, j: int, target: int)
        requires
            0 <= i < j < nums.len() - 1,
            Self::prefix_sum(nums, i + 1) == target,
            Self::prefix_sum(nums, j + 1) == 2 * target,
            Self::total_sum(nums) == 3 * target,
        ensures
            Self::valid_split_pair(nums, i, j),
    {
        assert(Self::prefix_sum(nums, j + 1) - Self::prefix_sum(nums, i + 1) == target);
        assert(Self::total_sum(nums) - Self::prefix_sum(nums, j + 1) == target);
    }

    proof fn lemma_valid_split_pair_properties(nums: Seq<i64>, i: int, j: int)
        requires
            Self::valid_split_pair(nums, i, j),
        ensures
            Self::prefix_sum(nums, j + 1) == 2 * Self::prefix_sum(nums, i + 1),
            Self::total_sum(nums) == 3 * Self::prefix_sum(nums, i + 1),
    {
        let s1 = Self::prefix_sum(nums, i + 1);
        let s2 = Self::prefix_sum(nums, j + 1) - Self::prefix_sum(nums, i + 1);
        let s3 = Self::total_sum(nums) - Self::prefix_sum(nums, j + 1);
        assert(s1 == s2);
        assert(s2 == s3);
        assert(Self::prefix_sum(nums, j + 1) == s1 + s2);
        assert(Self::total_sum(nums) == s1 + s2 + s3);
    }

    proof fn lemma_valid_split_pair_iff_prefix_targets(nums: Seq<i64>, i: int, j: int, target: int)
        requires
            0 <= i < j < nums.len() - 1,
            Self::total_sum(nums) == 3 * target,
        ensures
            Self::valid_split_pair(nums, i, j) == (Self::prefix_sum(nums, i + 1) == target && Self::prefix_sum(nums, j + 1) == 2 * target),
    {
        if Self::valid_split_pair(nums, i, j) {
            Self::lemma_valid_split_pair_properties(nums, i, j);
            assert(3 * Self::prefix_sum(nums, i + 1) == 3 * target);
            assert(Self::prefix_sum(nums, i + 1) == target);
        } else {
            if Self::prefix_sum(nums, i + 1) == target && Self::prefix_sum(nums, j + 1) == 2 * target {
                Self::lemma_prefix_targets_imply_valid_split_pair(nums, i, j, target);
                assert(false);
            }
        }
    }

    proof fn lemma_count_valid_first_cuts_match_target_prefixes(nums: Seq<i64>, target: int, j: int, i_end: int)
        requires
            0 <= i_end <= j,
            j < nums.len() - 1,
            Self::total_sum(nums) == 3 * target,
        ensures
            Self::count_valid_first_cuts(nums, j, i_end) == if Self::prefix_sum(nums, j + 1) == 2 * target {
                Self::count_target_prefixes(nums, target, i_end)
            } else {
                0nat
            },
        decreases i_end,
    {
        if i_end > 0 {
            Self::lemma_count_valid_first_cuts_match_target_prefixes(nums, target, j, i_end - 1);
            Self::lemma_valid_split_pair_iff_prefix_targets(nums, i_end - 1, j, target);
        }
    }

    proof fn lemma_count_valid_splits_match_prefix_counts(nums: Seq<i64>, target: int, end: int)
        requires
            0 <= end <= nums.len() - 1,
            Self::total_sum(nums) == 3 * target,
        ensures
            Self::count_valid_splits_upto(nums, end) == Self::count_prefix_split_pairs(nums, target, end),
        decreases end,
    {
        if end > 0 {
            Self::lemma_count_valid_splits_match_prefix_counts(nums, target, end - 1);
            Self::lemma_count_valid_first_cuts_match_target_prefixes(nums, target, end - 1, end - 1);
        }
    }

    proof fn lemma_count_valid_first_cuts_positive_implies_exists(nums: Seq<i64>, j: int, i_end: int)
        requires
            0 <= i_end <= j,
            j < nums.len() - 1,
        ensures
            Self::count_valid_first_cuts(nums, j, i_end) > 0 ==> exists |i: int| 0 <= i < i_end && #[trigger] Self::valid_split_pair(nums, i, j),
        decreases i_end,
    {
        if i_end > 0 {
            Self::lemma_count_valid_first_cuts_positive_implies_exists(nums, j, i_end - 1);
            if Self::count_valid_first_cuts(nums, j, i_end) > 0 {
                if Self::count_valid_first_cuts(nums, j, i_end - 1) > 0 {
                    assert(exists |i: int| 0 <= i < i_end - 1 && Self::valid_split_pair(nums, i, j));
                    let witness = choose |i: int| 0 <= i < i_end - 1 && Self::valid_split_pair(nums, i, j);
                    assert(0 <= witness < i_end && Self::valid_split_pair(nums, witness, j));
                } else {
                    assert(Self::valid_split_pair(nums, i_end - 1, j));
                    assert(exists |i: int| 0 <= i < i_end && Self::valid_split_pair(nums, i, j));
                }
            }
        }
    }

    proof fn lemma_count_valid_splits_positive_implies_exists(nums: Seq<i64>, end: int)
        requires
            0 <= end <= nums.len() - 1,
        ensures
            Self::count_valid_splits_upto(nums, end) > 0 ==> exists |i: int, j: int| 0 <= i < j < end && #[trigger] Self::valid_split_pair(nums, i, j),
        decreases end,
    {
        if end > 0 {
            Self::lemma_count_valid_splits_positive_implies_exists(nums, end - 1);
            Self::lemma_count_valid_first_cuts_positive_implies_exists(nums, end - 1, end - 1);
            if Self::count_valid_splits_upto(nums, end) > 0 {
                if Self::count_valid_splits_upto(nums, end - 1) > 0 {
                    assert(exists |i: int, j: int| 0 <= i < j < end - 1 && Self::valid_split_pair(nums, i, j));
                    assert(exists |i: int, j: int| 0 <= i < j < end && Self::valid_split_pair(nums, i, j)) by {
                        let witness = choose |i: int, j: int| 0 <= i < j < end - 1 && Self::valid_split_pair(nums, i, j);
                        assert(0 <= witness.0 < witness.1 < end);
                        assert(Self::valid_split_pair(nums, witness.0, witness.1));
                    };
                } else {
                    assert(Self::count_valid_first_cuts(nums, end - 1, end - 1) > 0);
                    assert(exists |i: int| 0 <= i < end - 1 && #[trigger] Self::valid_split_pair(nums, i, end - 1));
                    let witness = choose |i: int| 0 <= i < end - 1 && #[trigger] Self::valid_split_pair(nums, i, end - 1);
                    assert(0 <= witness < end - 1 < end && Self::valid_split_pair(nums, witness, end - 1));
                }
            }
        }
    }

    pub fn count_equal_sum_splits(nums: Vec<i64>) -> (result: u64)
        requires
            1 <= nums.len() <= 500_000,
            forall |k: int| 0 <= k < nums.len() ==> -1_000_000_000 <= #[trigger] nums[k] <= 1_000_000_000,
        ensures
            result as int == Self::count_valid_splits(nums@),
    {
        let n = nums.len();
        if n < 3 {
            proof {
                assert(Self::count_valid_splits(nums@) == 0);
            }
            return 0;
        }

        let mut total: i128 = 0;
        let mut idx: usize = 0;
        while idx < n
            invariant
                n == nums.len(),
                3 <= n <= 500_000,
                0 <= idx <= n,
                forall |k: int| 0 <= k < n ==> -1_000_000_000 <= #[trigger] nums[k] <= 1_000_000_000,
                total as int == Self::prefix_sum(nums@, idx as int),
                -1_000_000_000 * idx as int <= total as int <= 1_000_000_000 * idx as int,
            decreases n - idx,
        {
            proof {
                Self::lemma_prefix_sum_step(nums@, idx as int);
            }
            total = total + nums[idx] as i128;
            idx = idx + 1;
        }

        let target = total / 3;
        if target * 3 != total {
            proof {
                assert(total as int == Self::total_sum(nums@));
                assert(!(exists |i: int, j: int| 0 <= i < j < nums@.len() - 1 && Self::valid_split_pair(nums@, i, j))) by {
                    assert forall |i: int, j: int| 0 <= i < j < nums@.len() - 1 && Self::valid_split_pair(nums@, i, j) implies false by {
                        Self::lemma_valid_split_pair_properties(nums@, i, j);
                        assert(total as int == 3 * Self::prefix_sum(nums@, i + 1));
                        assert(total == 3 * (Self::prefix_sum(nums@, i + 1) as i128));
                        assert(target * 3 == total);
                    }
                };
                assert(Self::count_valid_splits(nums@) == Self::count_valid_splits_upto(nums@, nums@.len() - 1));
                if Self::count_valid_splits(nums@) > 0 {
                    Self::lemma_count_valid_splits_positive_implies_exists(nums@, nums@.len() - 1);
                    assert(exists |i: int, j: int| 0 <= i < j < nums@.len() - 1 && Self::valid_split_pair(nums@, i, j));
                }
                assert(Self::count_valid_splits(nums@) == 0);
            }
            return 0;
        }

        proof {
            assert(total as int == Self::total_sum(nums@));
            assert(total as int == 3 * target as int);
        }

        let mut prefix: i128 = 0;
        let mut seen_targets: u64 = 0;
        let mut answer: u64 = 0;
        idx = 0;
        while idx < n - 1
            invariant
                n == nums.len(),
                3 <= n <= 500_000,
                0 <= idx <= n - 1,
                forall |k: int| 0 <= k < n ==> -1_000_000_000 <= #[trigger] nums[k] <= 1_000_000_000,
                total as int == Self::total_sum(nums@),
                total as int == 3 * target as int,
                prefix as int == Self::prefix_sum(nums@, idx as int),
                -1_000_000_000 * idx as int <= prefix as int <= 1_000_000_000 * idx as int,
                seen_targets as int == Self::count_target_prefixes(nums@, target as int, idx as int),
                seen_targets as int <= idx as int,
                answer as int == Self::count_prefix_split_pairs(nums@, target as int, idx as int),
                answer as int <= idx as int * idx as int,
            decreases n - 1 - idx,
        {
            let prev_seen = seen_targets;
            let prev_answer = answer;
            proof {
                Self::lemma_prefix_sum_step(nums@, idx as int);
            }
            prefix = prefix + nums[idx] as i128;
            if prefix == target + target {
                proof {
                    assert(answer as int + seen_targets as int <= idx as int * idx as int + idx as int);
                    assert(idx as int + 1 <= n as int);
                    assert(idx as int * idx as int + idx as int <= n as int * n as int) by (nonlinear_arith)
                        requires
                            0 <= idx as int,
                            idx as int + 1 <= n as int,
                    ;
                    assert(n as int * n as int <= 250000000000) by (nonlinear_arith)
                        requires
                            0 <= n as int,
                            n as int <= 500000,
                    ;
                }
                answer = answer + seen_targets;
            }
            if prefix == target {
                seen_targets = seen_targets + 1;
            }
            proof {
                assert(prefix as int == Self::prefix_sum(nums@, idx as int + 1));
                assert(Self::count_target_prefixes(nums@, target as int, idx as int + 1) == Self::count_target_prefixes(nums@, target as int, idx as int) + if Self::prefix_sum(nums@, idx as int + 1) == target as int {
                    1nat
                } else {
                    0nat
                });
                if prefix == target {
                    assert(seen_targets == prev_seen + 1);
                    assert(Self::prefix_sum(nums@, idx as int + 1) == target as int);
                } else {
                    assert(seen_targets == prev_seen);
                    assert(Self::prefix_sum(nums@, idx as int + 1) != target as int);
                }
                assert(Self::count_prefix_split_pairs(nums@, target as int, idx as int + 1) == Self::count_prefix_split_pairs(nums@, target as int, idx as int) + if Self::prefix_sum(nums@, idx as int + 1) == 2 * target as int {
                    Self::count_target_prefixes(nums@, target as int, idx as int)
                } else {
                    0nat
                });
                if prefix == target + target {
                    assert(answer as int == prev_answer as int + prev_seen as int);
                    assert(prefix as int == 2 * target as int) by (nonlinear_arith)
                        requires
                            prefix == target + target,
                    ;
                    assert(Self::prefix_sum(nums@, idx as int + 1) == 2 * target as int);
                    assert(answer as int <= idx as int * idx as int + idx as int);
                } else {
                    assert(answer as int == prev_answer as int);
                    assert(Self::prefix_sum(nums@, idx as int + 1) != 2 * target as int);
                    assert(answer as int <= idx as int * idx as int + idx as int);
                }
                assert(seen_targets as int == Self::count_target_prefixes(nums@, target as int, idx as int + 1));
                assert(answer as int == Self::count_prefix_split_pairs(nums@, target as int, idx as int + 1));
                assert(seen_targets as int <= idx as int + 1);
                assert(answer as int <= (idx as int + 1) * (idx as int + 1)) by (nonlinear_arith)
                    requires
                        0 <= idx as int,
                        answer as int <= idx as int * idx as int + idx as int,
                ;
            }
            idx = idx + 1;
        }

        proof {
            Self::lemma_count_valid_splits_match_prefix_counts(nums@, target as int, n as int - 1);
            assert(Self::count_valid_splits(nums@) == Self::count_valid_splits_upto(nums@, n as int - 1));
            assert(answer as int == Self::count_valid_splits(nums@));
        }
        answer
    }
}

}
