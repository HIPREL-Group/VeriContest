use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_occurrences(s: Seq<i32>, value: i32) -> nat
        decreases s.len()
    {
        if s.len() == 0 {
            0
        } else {
            Self::count_occurrences(s.drop_last(), value) + if s.last() == value { 1 as nat } else { 0 as nat }
        }
    }

    proof fn lemma_count_extend(s: Seq<i32>, value: i32, elem: i32)
        ensures
            Self::count_occurrences(s.push(elem), value) == Self::count_occurrences(s, value) + if elem == value { 1 as nat } else { 0 as nat },
    {
        assert(s.push(elem).drop_last() =~= s);
    }

    proof fn lemma_count_occurrences_at_least_one(s: Seq<i32>, value: i32, idx: int)
        requires
            0 <= idx < s.len(),
            s[idx] == value,
        ensures
            Self::count_occurrences(s, value) >= 1,
        decreases s.len(),
    {
        if s.len() == 1 {
        } else if idx == s.len() - 1 {
            assert(s.last() == value);
        } else {
            Self::lemma_count_occurrences_at_least_one(s.drop_last(), value, idx);
        }
    }

    proof fn lemma_count_occurrences_at_least_two(s: Seq<i32>, value: i32, i: int, j: int)
        requires
            0 <= i < j < s.len(),
            s[i] == value,
            s[j] == value,
        ensures
            Self::count_occurrences(s, value) >= 2,
        decreases s.len(),
    {
        if j == s.len() - 1 {
            Self::lemma_count_occurrences_at_least_one(s.drop_last(), value, i);
            assert(s.last() == value);
        } else {
            Self::lemma_count_occurrences_at_least_two(s.drop_last(), value, i, j);
        }
    }

    pub open spec fn valid_input(nums: Seq<i32>) -> bool {
        4 <= nums.len() <= 10_000 &&
        nums.len() % 2 == 0 &&
        exists |k: int|
            0 <= k < nums.len() &&
            (forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 10_000) &&
            Self::count_occurrences(nums, nums[k]) == nums.len() / 2 &&
            (forall |i: int| 0 <= i < nums.len() && nums[i] != nums[k] ==> #[trigger] Self::count_occurrences(nums, nums[i]) == 1)
    }

    pub open spec fn sparse_step(nums: Seq<i32>, value: i32, i: int) -> bool
        recommends
            2 <= i < nums.len(),
    {
        nums[i] == value ==> nums[i - 1] != value && nums[i - 2] != value
    }

    pub open spec fn detect_step(nums: Seq<i32>, value: i32, i: int) -> bool
        recommends
            2 <= i < nums.len(),
    {
        nums[i] == value && (nums[i - 1] == value || nums[i - 2] == value)
    }

    pub open spec fn gap_step(nums: Seq<i32>, i: int) -> bool
        recommends
            2 <= i < nums.len(),
    {
        nums[i] != nums[i - 1] && nums[i] != nums[i - 2]
    }

    proof fn lemma_duplicate_pair_is_repeated(nums: Seq<i32>, i: int, j: int)
        requires
            Self::valid_input(nums),
            0 <= i < j < nums.len(),
            nums[i] == nums[j],
        ensures
            Self::count_occurrences(nums, nums[i]) == nums.len() / 2,
    {
        let k = choose |k: int|
            4 <= nums.len() <= 10_000 &&
            nums.len() % 2 == 0 &&
            0 <= k < nums.len() &&
            (forall |m: int| 0 <= m < nums.len() ==> 0 <= #[trigger] nums[m] <= 10_000) &&
            Self::count_occurrences(nums, nums[k]) == nums.len() / 2 &&
            (forall |m: int| 0 <= m < nums.len() && nums[m] != nums[k] ==> #[trigger] Self::count_occurrences(nums, nums[m]) == 1);
        let repeated = nums[k];
        if nums[i] != repeated {
            assert(Self::count_occurrences(nums, nums[i]) == 1);
            Self::lemma_count_occurrences_at_least_two(nums, nums[i], i, j);
            assert(false);
        }
        assert(nums[i] == repeated);
        assert(Self::count_occurrences(nums, nums[i]) == nums.len() / 2);
    }

    proof fn lemma_sparse_occurrence_bound(nums: Seq<i32>, value: i32)
        requires
            nums.len() == 0 || nums[0] != value,
            forall |i: int| 2 <= i < nums.len() ==> #[trigger] Self::sparse_step(nums, value, i),
        ensures
            Self::count_occurrences(nums, value) as int <= (nums.len() + 1) / 3,
        decreases nums.len(),
    {
        if nums.len() == 0 {
        } else if nums.last() != value {
            let prefix = nums.drop_last();
            assert forall |i: int| 2 <= i < prefix.len() implies #[trigger] Self::sparse_step(prefix, value, i) by {
                assert(Self::sparse_step(nums, value, i));
                assert(prefix[i] == nums[i]);
                assert(prefix[i - 1] == nums[i - 1]);
                assert(prefix[i - 2] == nums[i - 2]);
            }
            Self::lemma_sparse_occurrence_bound(prefix, value);
            assert(Self::count_occurrences(nums, value) == Self::count_occurrences(prefix, value));
        } else {
            assert(nums.len() >= 2);
            if nums.len() == 2 {
                assert(nums[0] != value);
                let prefix = nums.drop_last();
                assert(prefix.len() == 1);
                assert(prefix.last() == nums[0]);
                assert(prefix.last() != value);
                assert(prefix.drop_last() =~= Seq::<i32>::empty());
                assert(Self::count_occurrences(prefix.drop_last(), value) == 0);
                assert(Self::count_occurrences(prefix, value) == 0);
                assert(Self::count_occurrences(nums, value) == 1);
            } else {
                assert(Self::sparse_step(nums, value, nums.len() - 1));
                assert(nums[nums.len() - 2] != value);
                assert(nums[nums.len() - 3] != value);
                let prefix = nums.drop_last().drop_last().drop_last();
                assert forall |i: int| 2 <= i < prefix.len() implies #[trigger] Self::sparse_step(prefix, value, i) by {
                    assert(Self::sparse_step(nums, value, i));
                    assert(prefix[i] == nums[i]);
                    assert(prefix[i - 1] == nums[i - 1]);
                    assert(prefix[i - 2] == nums[i - 2]);
                }
                Self::lemma_sparse_occurrence_bound(prefix, value);
                assert(Self::count_occurrences(nums.drop_last(), value) == Self::count_occurrences(nums.drop_last().drop_last(), value));
                assert(Self::count_occurrences(nums.drop_last().drop_last(), value) == Self::count_occurrences(prefix, value));
                assert(Self::count_occurrences(nums, value) == Self::count_occurrences(prefix, value) + 1);
                assert(Self::count_occurrences(prefix, value) as int <= (prefix.len() + 1) / 3);
                assert(prefix.len() == nums.len() - 3);
                assert(Self::count_occurrences(nums, value) as int <= (nums.len() + 1) / 3);
            }
        }
    }

    proof fn lemma_detectable_if_not_first(nums: Seq<i32>, value: i32)
        requires
            4 <= nums.len(),
            nums.len() % 2 == 0,
            nums[0] != value,
            Self::count_occurrences(nums, value) == nums.len() / 2,
        ensures
            exists |i: int| 2 <= i < nums.len() && #[trigger] Self::detect_step(nums, value, i),
    {
        if !(exists |i: int| 2 <= i < nums.len() && #[trigger] Self::detect_step(nums, value, i)) {
            assert forall |i: int| 2 <= i < nums.len() implies #[trigger] Self::sparse_step(nums, value, i) by {
                if nums[i] == value {
                    if nums[i - 1] == value || nums[i - 2] == value {
                        assert(Self::detect_step(nums, value, i));
                        assert(false);
                    }
                }
            }
            Self::lemma_sparse_occurrence_bound(nums, value);
            assert(Self::count_occurrences(nums, value) as int <= (nums.len() + 1) / 3);
            assert(Self::count_occurrences(nums, value) as int == nums.len() / 2);
            assert(3 * (nums.len() / 2) > nums.len() + 1);
            assert(false);
        }
    }

    proof fn lemma_no_detection_means_first_is_repeated(nums: Seq<i32>)
        requires
            Self::valid_input(nums),
            forall |i: int| 2 <= i < nums.len() ==> #[trigger] Self::gap_step(nums, i),
        ensures
            Self::count_occurrences(nums, nums[0]) == nums.len() / 2,
    {
        let k = choose |k: int|
            4 <= nums.len() <= 10_000 &&
            nums.len() % 2 == 0 &&
            0 <= k < nums.len() &&
            (forall |m: int| 0 <= m < nums.len() ==> 0 <= #[trigger] nums[m] <= 10_000) &&
            Self::count_occurrences(nums, nums[k]) == nums.len() / 2 &&
            (forall |m: int| 0 <= m < nums.len() && nums[m] != nums[k] ==> #[trigger] Self::count_occurrences(nums, nums[m]) == 1);
        let repeated = nums[k];
        if nums[0] != repeated {
            Self::lemma_detectable_if_not_first(nums, repeated);
            let i = choose |i: int| 2 <= i < nums.len() && #[trigger] Self::detect_step(nums, repeated, i);
            assert(Self::gap_step(nums, i));
            if nums[i - 1] == repeated {
                assert(nums[i] == nums[i - 1]);
                assert(nums[i] != nums[i - 1]);
            } else {
                assert(nums[i] == nums[i - 2]);
                assert(nums[i] != nums[i - 2]);
            }
            assert(false);
        }
        assert(Self::count_occurrences(nums, nums[0]) == nums.len() / 2);
    }

    pub fn repeated_n_times(nums: Vec<i32>) -> (res: i32)
        requires
            Self::valid_input(nums@),
        ensures
            Self::count_occurrences(nums@, res) == nums.len() / 2,
    {
        let n = nums.len();
        let mut i: usize = 2;

        while i < n
            invariant
                Self::valid_input(nums@),
                n == nums.len(),
                2 <= i <= n,
                forall |j: int| 2 <= j < i ==> #[trigger] Self::gap_step(nums@, j),
            decreases n - i,
        {
            if nums[i] == nums[i - 1] {
                proof {
                    Self::lemma_duplicate_pair_is_repeated(nums@, i as int - 1, i as int);
                }
                return nums[i];
            }
            if nums[i] == nums[i - 2] {
                proof {
                    Self::lemma_duplicate_pair_is_repeated(nums@, i as int - 2, i as int);
                }
                return nums[i];
            }
            i += 1;
        }

        proof {
            Self::lemma_no_detection_means_first_is_repeated(nums@);
        }
        nums[0]
    }
}

}
