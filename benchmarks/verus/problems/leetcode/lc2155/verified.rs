use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_zeros(nums: Seq<i32>, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            (if nums[end - 1] == 0 { 1int } else { 0int }) + Self::count_zeros(nums, end - 1)
        }
    }

    pub open spec fn count_ones(nums: Seq<i32>, start: int, end: int) -> int
        decreases end - start,
    {
        if start >= end {
            0
        } else {
            (if nums[start] == 1 { 1int } else { 0int }) + Self::count_ones(nums, start + 1, end)
        }
    }

    pub open spec fn div_score(nums: Seq<i32>, i: int) -> int {
        Self::count_zeros(nums, i) + Self::count_ones(nums, i, nums.len() as int)
    }

    proof fn lemma_count_ones_split(nums: Seq<i32>, l: int, m: int, r: int)
        requires
            0 <= l <= m <= r <= nums.len(),
        ensures
            Self::count_ones(nums, l, r) == Self::count_ones(nums, l, m) + Self::count_ones(nums, m, r),
        decreases m - l,
    {
        if l < m {
            Self::lemma_count_ones_split(nums, l + 1, m, r);
        }
    }

    proof fn lemma_count_ones_nonneg(nums: Seq<i32>, l: int, r: int)
        requires
            0 <= l <= r <= nums.len(),
        ensures
            Self::count_ones(nums, l, r) >= 0,
        decreases r - l,
    {
        if l < r {
            Self::lemma_count_ones_nonneg(nums, l + 1, r);
        }
    }

    proof fn lemma_count_ones_upper(nums: Seq<i32>, l: int, r: int)
        requires
            0 <= l <= r <= nums.len(),
        ensures
            Self::count_ones(nums, l, r) <= r - l,
        decreases r - l,
    {
        if l < r {
            Self::lemma_count_ones_upper(nums, l + 1, r);
        }
    }

    proof fn lemma_count_zeros_nonneg(nums: Seq<i32>, end: int)
        requires
            0 <= end <= nums.len(),
        ensures
            Self::count_zeros(nums, end) >= 0,
        decreases end,
    {
        if end > 0 {
            Self::lemma_count_zeros_nonneg(nums, end - 1);
        }
    }

    proof fn lemma_count_zeros_upper(nums: Seq<i32>, end: int)
        requires
            0 <= end <= nums.len(),
        ensures
            Self::count_zeros(nums, end) <= end,
        decreases end,
    {
        if end > 0 {
            Self::lemma_count_zeros_upper(nums, end - 1);
        }
    }

    pub fn max_score_indices(nums: Vec<i32>) -> (res: Vec<i32>)
        requires
            1 <= nums.len() <= 100000,
            forall|i: int| 0 <= i < nums.len() ==> #[trigger] nums[i] == 0 || nums[i] == 1,
        ensures
            res.len() >= 1,
            forall|j: int| 0 <= j < res.len() ==> 0 <= #[trigger] res[j] <= nums@.len() as i32,
            forall|j: int| 0 <= j < res.len() ==> Self::div_score(nums@, (#[trigger] res[j]) as int) == Self::div_score(nums@, res[0] as int),
            forall|k: int| 0 <= k <= nums@.len() as int ==> Self::div_score(nums@, res[0] as int) >= #[trigger] Self::div_score(nums@, k),
            forall|k: int| 0 <= k <= nums@.len() as int && #[trigger] Self::div_score(nums@, k) == Self::div_score(nums@, res[0] as int) ==> exists|j: int| 0 <= j < res.len() && #[trigger] res[j] == k as i32,
            forall|j1: int, j2: int| 0 <= j1 < res.len() && 0 <= j2 < res.len() && j1 != j2 ==> #[trigger] res[j1] != #[trigger] res[j2],
    {
        let mut total_ones = 0i32;
        assert(nums.len() <= 100000usize);
        let mut i: usize = 0;
        while i < nums.len()
            invariant
                i <= nums.len(),
                nums.len() <= 100000usize,
                0 <= total_ones <= i as i32,
                total_ones as int == Self::count_ones(nums@, 0, i as int),
                forall|ii: int| 0 <= ii < nums.len() ==> #[trigger] nums[ii] == 0 || nums[ii] == 1,
            decreases nums.len() - i,
        {
            proof {
                Self::lemma_count_ones_split(nums@, 0, i as int, i as int + 1);
                assert(Self::count_ones(nums@, i as int + 1, i as int + 1) == 0int);
            }
            if nums[i] == 1 {
                total_ones = total_ones + 1;
            }
            i = i + 1;
        }

        let mut max_score = -1i32;
        let mut left_zeros = 0i32;
        let mut right_ones = total_ones;

        let mut scores = Vec::new();
        let mut indices: Vec<i32> = Vec::new();

        let mut idx: usize = 0;
        let ghost mut max_idx: int = -1;

        proof {
            Self::lemma_count_zeros_nonneg(nums@, 0);
            Self::lemma_count_ones_nonneg(nums@, 0, nums@.len() as int);
        }

        while idx <= nums.len()
            invariant
                nums.len() <= 100000usize,
                idx <= nums.len() + 1,
                scores.len() == idx,
                0 <= total_ones <= nums.len() as i32,
                total_ones as int == Self::count_ones(nums@, 0, nums@.len() as int),
                forall|ii: int| 0 <= ii < nums.len() ==> #[trigger] nums[ii] == 0 || nums[ii] == 1,
                idx <= nums.len() ==> left_zeros as int == Self::count_zeros(nums@, idx as int),
                idx <= nums.len() ==> right_ones as int == Self::count_ones(nums@, idx as int, nums@.len() as int),
                0 <= left_zeros <= idx as i32,
                0 <= right_ones <= total_ones,
                -1 <= max_score <= 200000,
                forall|k: int| 0 <= k < idx as int ==> #[trigger] scores[k] as int == Self::div_score(nums@, k),
                forall|k: int| 0 <= k < idx as int ==> max_score as int >= scores[k] as int,
                idx > 0 ==> (0 <= max_idx < idx as int && scores[max_idx] == max_score && max_score >= 0),
                idx == 0 ==> max_score == -1i32,
            decreases nums.len() - idx + 1,
        {
            let score = left_zeros + right_ones;
            assert(score as int == Self::div_score(nums@, idx as int));

            let ghost scores_before = scores@;
            scores.push(score);

            assert(score >= 0i32);

            if score > max_score {
                max_score = score;
                proof { max_idx = idx as int; }
            } else {
                // score <= max_score >= score >= 0, so max_score >= 0
                // Since max_score > -1 (initial), we must have updated it before, so idx > 0
                proof {
                    assert(max_score >= 0);
                    // old invariant (idx > 0) gives us valid max_idx
                    assert(0 <= max_idx && max_idx < idx as int);
                    assert(scores@[max_idx] == scores_before[max_idx]);
                }
            }

            // At this point: 0 <= max_idx <= idx, scores[max_idx] == max_score, max_score >= 0
            assert(scores[max_idx] == max_score);
            assert(0 <= max_idx && max_idx <= idx as int);
            assert(max_score >= 0);

            if idx < nums.len() {
                proof {
                    Self::lemma_count_zeros_nonneg(nums@, idx as int + 1);
                    Self::lemma_count_zeros_upper(nums@, idx as int + 1);
                    Self::lemma_count_ones_nonneg(nums@, idx as int + 1, nums@.len() as int);
                    Self::lemma_count_ones_upper(nums@, idx as int + 1, nums@.len() as int);
                }
                if nums[idx] == 0 {
                    left_zeros = left_zeros + 1;
                } else {
                    right_ones = right_ones - 1;
                }
            }

            assert(idx <= nums.len());
            idx = idx + 1;
        }

        assert(scores.len() == nums.len() + 1);
        assert(scores.len() <= 100001);
        assert(0 <= max_idx < scores.len() as int && scores[max_idx] == max_score);

        idx = 0;
        while idx < scores.len()
            invariant
                idx <= scores.len(),
                scores.len() == nums.len() + 1,
                scores.len() <= 100001,
                0 <= max_score <= 200000,
                forall|ii: int| 0 <= ii < nums.len() ==> #[trigger] nums[ii] == 0 || nums[ii] == 1,
                forall|k: int| 0 <= k < scores.len() as int ==> #[trigger] scores[k] as int == Self::div_score(nums@, k),
                forall|k: int| 0 <= k < scores.len() as int ==> max_score as int >= scores[k] as int,
                0 <= max_idx < scores.len() as int && scores[max_idx] == max_score,
                forall|m: int| 0 <= m < indices.len() ==> (
                    0 <= #[trigger] indices[m] < idx as i32
                    && indices[m] <= nums@.len() as i32
                    && scores[indices[m] as int] == max_score
                ),
                forall|k: int| 0 <= k < idx as int && scores[k] == max_score ==>
                    exists|m: int| 0 <= m < indices.len() && #[trigger] indices[m] == k as i32,
                forall|m1: int, m2: int| 0 <= m1 < indices.len() && 0 <= m2 < indices.len() && m1 != m2 ==> #[trigger] indices[m1] != #[trigger] indices[m2],
                forall|m1: int, m2: int| 0 <= m1 < m2 < indices.len() ==> #[trigger] indices[m1] < #[trigger] indices[m2],
            decreases scores.len() - idx,
        {
            if scores[idx] == max_score {
                let ghost old_len = indices.len();
                let ghost old_indices = indices@;
                assert(forall|m: int| 0 <= m < old_len ==> #[trigger] indices[m] < idx as i32);
                indices.push(idx as i32);
                // indices@ == old_indices.push(idx as i32)
                // For m < old_len: indices[m] == old_indices[m]

                proof {
                    // Prove old witnesses still valid after push
                    assert(forall|m: int| 0 <= m < old_len ==> indices@[m] == old_indices[m]);

                    assert forall|k: int| 0 <= k < idx as int + 1 && scores[k] == max_score implies
                        exists|m: int| 0 <= m < indices.len() && #[trigger] indices[m] == k as i32
                    by {
                        if k == idx as int {
                            assert(indices[indices.len() - 1] == idx as i32);
                        } else {
                            // k < idx, old invariant had: exists m < old_len with old_indices[m] == k as i32
                            // After push: indices[m] == old_indices[m] for m < old_len
                            // So same m works with indices.len() > old_len
                        }
                    };
                }
            }
            idx = idx + 1;
        }

        // indices contains exactly the max-scoring positions
        assert(indices.len() >= 1) by {
            assert(0 <= max_idx < scores.len() as int && scores[max_idx] == max_score);
            assert(max_idx < idx as int);
        };

        // All result elements have div_score == max_score
        proof {
            assert forall|j: int| 0 <= j < indices.len() implies
                Self::div_score(nums@, (#[trigger] indices[j]) as int) == max_score as int
            by {
                let v = indices[j];
                assert(scores[v as int] == max_score);
                assert(scores[v as int] as int == Self::div_score(nums@, v as int));
            };
        }

        assert(forall|j: int| 0 <= j < indices.len() ==> Self::div_score(nums@, (#[trigger] indices[j]) as int) == Self::div_score(nums@, indices[0] as int));

        proof {
            assert forall|k: int| 0 <= k <= nums@.len() as int implies
                Self::div_score(nums@, indices[0] as int) >= #[trigger] Self::div_score(nums@, k)
            by {
                assert(Self::div_score(nums@, indices[0] as int) == max_score as int);
                assert(scores[k] as int == Self::div_score(nums@, k));
                assert(max_score as int >= scores[k] as int);
            };
        }

        proof {
            assert forall|k: int| 0 <= k <= nums@.len() as int && #[trigger] Self::div_score(nums@, k) == Self::div_score(nums@, indices[0] as int) implies
                exists|j: int| 0 <= j < indices.len() && #[trigger] indices[j] == k as i32
            by {
                assert(Self::div_score(nums@, indices[0] as int) == max_score as int);
                assert(Self::div_score(nums@, k) == max_score as int);
                assert(scores[k] as int == Self::div_score(nums@, k));
                assert(scores[k] as int == max_score as int);
                assert(scores[k] == max_score);
                assert(k < scores.len() as int);
            };
        }

        indices
    }
}
}
