use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn same_parity_adjacent(nums: Seq<i32>, i: int) -> bool
        recommends
            0 <= i + 1 < nums.len(),
    {
        nums[i] % 2 == nums[i + 1] % 2
    }

    pub open spec fn query_is_special(nums: Seq<i32>, query: Vec<i32>) -> bool
        recommends
            query@.len() == 2,
            0 <= query@[0] <= query@[1] < nums.len(),
    {
        forall |k: int| query@[0] <= k < query@[1] ==> !(#[trigger] Self::same_parity_adjacent(nums, k))
    }

    pub open spec fn bad_step(nums: Seq<i32>, i: int) -> int
        recommends
            0 <= i + 1 < nums.len(),
    {
        if Self::same_parity_adjacent(nums, i) { 1 } else { 0 }
    }

    pub open spec fn bad_prefix(nums: Seq<i32>, end: int) -> int
        recommends
            0 <= end < nums.len(),
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::bad_prefix(nums, end - 1) + Self::bad_step(nums, end - 1)
        }
    }

    proof fn lemma_bad_prefix_monotonic(nums: Seq<i32>, left: int, right: int)
        requires
            0 <= left <= right < nums.len(),
        ensures
            Self::bad_prefix(nums, left) <= Self::bad_prefix(nums, right),
        decreases right - left,
    {
        if left < right {
            Self::lemma_bad_prefix_monotonic(nums, left, right - 1);
            assert(Self::bad_prefix(nums, right) == Self::bad_prefix(nums, right - 1) + Self::bad_step(nums, right - 1));
            assert(0 <= Self::bad_step(nums, right - 1));
        }
    }

    proof fn lemma_bad_prefix_difference_has_bad(nums: Seq<i32>, left: int, right: int)
        requires
            0 <= left <= right < nums.len(),
            Self::bad_prefix(nums, left) < Self::bad_prefix(nums, right),
        ensures
            exists |k: int| left <= k < right && #[trigger] Self::same_parity_adjacent(nums, k),
        decreases right - left,
    {
        if left == right {
            assert(false);
        } else if Self::same_parity_adjacent(nums, right - 1) {
            assert(left <= right - 1 < right);
        } else {
            assert(Self::bad_step(nums, right - 1) == 0);
            assert(Self::bad_prefix(nums, right) == Self::bad_prefix(nums, right - 1));
            Self::lemma_bad_prefix_difference_has_bad(nums, left, right - 1);
        }
    }

    pub fn is_array_special(nums: Vec<i32>, queries: Vec<Vec<i32>>) -> (answer: Vec<bool>)
        requires
            1 <= nums.len() <= 100_000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100_000,
            1 <= queries.len() <= 100_000,
            forall |i: int| 0 <= i < queries.len() ==>
                queries[i].len() == 2
                && 0 <= queries[i][0] <= queries[i][1] < nums.len(),
        ensures
            answer.len() == queries.len(),
            forall |i: int| 0 <= i < queries.len() ==> #[trigger] answer[i] == Self::query_is_special(nums@, queries[i]),
    {
        let n = nums.len();
        let mut prefix: Vec<i32> = Vec::new();
        prefix.push(0);

        let mut i: usize = 1;
        while i < n
            invariant
                n == nums.len(),
                1 <= nums.len() <= 100_000,
                1 <= i <= nums.len(),
                prefix.len() == i,
                0 <= prefix[i as int - 1] as int <= i as int - 1,
                forall |j: int| 0 <= j < nums.len() ==> 1 <= #[trigger] nums[j] <= 100_000,
                forall |j: int| 0 <= j < prefix.len() ==> #[trigger] prefix[j] as int == Self::bad_prefix(nums@, j),
            decreases n - i,
        {
            let mut next = prefix[i - 1];
            let prev_val = nums[i - 1];
            let curr_val = nums[i];
            if prev_val % 2 == curr_val % 2 {
                proof {
                    assert(0 <= prefix[i as int - 1] as int <= i as int - 1);
                    assert(next as int == prefix[i as int - 1] as int);
                    assert(i as int - 1 < 100_000);
                    assert(next < 2_147_483_647);
                }
                next = next + 1;
            }
            let ghost prefix_before = prefix@;
            prefix.push(next);
            proof {
                assert(prefix@ == prefix_before.push(next));
                assert(Self::bad_prefix(nums@, i as int) == Self::bad_prefix(nums@, i as int - 1) + Self::bad_step(nums@, i as int - 1));
                assert(prefix[i as int - 1] as int == Self::bad_prefix(nums@, i as int - 1));
                assert(prev_val == nums[i as int - 1]);
                assert(curr_val == nums[i as int]);
                if prev_val % 2 == curr_val % 2 {
                    assert(Self::same_parity_adjacent(nums@, i as int - 1));
                    assert(Self::bad_step(nums@, i as int - 1) == 1);
                    assert(next as int == prefix[i as int - 1] as int + 1);
                } else {
                    assert(!Self::same_parity_adjacent(nums@, i as int - 1));
                    assert(Self::bad_step(nums@, i as int - 1) == 0);
                    assert(next as int == prefix[i as int - 1] as int);
                }
                assert(next as int == Self::bad_prefix(nums@, i as int));
                assert(0 <= next as int <= i as int);
            }
            i = i + 1;
        }

        let mut answer: Vec<bool> = Vec::new();
        let mut q: usize = 0;
        while q < queries.len()
            invariant
                n == nums.len(),
                prefix.len() == nums.len(),
                1 <= nums.len() <= 100_000,
                1 <= queries.len() <= 100_000,
                0 <= q <= queries.len(),
                answer.len() == q,
                forall |j: int| 0 <= j < nums.len() ==> 1 <= #[trigger] nums[j] <= 100_000,
                forall |j: int| 0 <= j < queries.len() ==>
                    queries[j].len() == 2
                    && 0 <= queries[j][0] <= queries[j][1] < nums.len(),
                forall |j: int| 0 <= j < prefix.len() ==> #[trigger] prefix[j] as int == Self::bad_prefix(nums@, j),
                forall |j: int| 0 <= j < q ==> #[trigger] answer[j] == Self::query_is_special(nums@, queries[j]),
            decreases queries.len() - q,
        {
            let left_i = queries[q][0];
            let right_i = queries[q][1];
            let left = left_i as usize;
            let right = right_i as usize;
            let is_special = prefix[left] == prefix[right];

            proof {
                assert(queries[q as int].len() == 2);
                assert(0 <= left_i <= right_i < nums.len());
                assert(prefix[left as int] as int == Self::bad_prefix(nums@, left_i as int));
                assert(prefix[right as int] as int == Self::bad_prefix(nums@, right_i as int));
                if is_special {
                    assert(Self::bad_prefix(nums@, left_i as int) == Self::bad_prefix(nums@, right_i as int));
                    assert(Self::query_is_special(nums@, queries[q as int])) by {
                        assert forall |k: int| left_i as int <= k < right_i as int implies !Self::same_parity_adjacent(nums@, k) by {
                            if Self::same_parity_adjacent(nums@, k) {
                                Self::lemma_bad_prefix_monotonic(nums@, left_i as int, k);
                                Self::lemma_bad_prefix_monotonic(nums@, k + 1, right_i as int);
                                assert(Self::bad_prefix(nums@, k + 1) == Self::bad_prefix(nums@, k) + Self::bad_step(nums@, k));
                                assert(Self::bad_step(nums@, k) == 1);
                                assert(Self::bad_prefix(nums@, left_i as int) <= Self::bad_prefix(nums@, k));
                                assert(Self::bad_prefix(nums@, k + 1) <= Self::bad_prefix(nums@, right_i as int));
                                assert(Self::bad_prefix(nums@, left_i as int) < Self::bad_prefix(nums@, right_i as int));
                                assert(false);
                            }
                        }
                    };
                } else {
                    Self::lemma_bad_prefix_monotonic(nums@, left_i as int, right_i as int);
                    assert(Self::bad_prefix(nums@, left_i as int) < Self::bad_prefix(nums@, right_i as int));
                    Self::lemma_bad_prefix_difference_has_bad(nums@, left_i as int, right_i as int);
                    let k = choose |k: int| left_i as int <= k < right_i as int && Self::same_parity_adjacent(nums@, k);
                    assert(left_i as int <= k < right_i as int && Self::same_parity_adjacent(nums@, k));
                    assert(!Self::query_is_special(nums@, queries[q as int])) by {
                        if Self::query_is_special(nums@, queries[q as int]) {
                            assert(!Self::same_parity_adjacent(nums@, k));
                            assert(false);
                        }
                    };
                }
            }

            let ghost answer_before = answer@;
            answer.push(is_special);
            proof {
                assert(answer@ == answer_before.push(is_special));
            }
            q = q + 1;
        }

        answer
    }
}

}