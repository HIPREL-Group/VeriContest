use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn contains(nums: Seq<i32>, value: i32) -> bool {
        exists |j: int| 0 <= j < nums.len() && #[trigger] nums[j] == value
    }

    pub open spec fn sequential_prefix_len(nums: Seq<i32>) -> nat
        decreases nums.len(),
    {
        if nums.len() == 0 {
            0nat
        } else if nums.len() == 1 {
            1nat
        } else if nums[1] == nums[0] + 1 {
            1nat + Self::sequential_prefix_len(nums.subrange(1, nums.len() as int))
        } else {
            1nat
        }
    }

    pub open spec fn prefix_sum(nums: Seq<i32>, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0int
        } else {
            Self::prefix_sum(nums, end - 1) + nums[end - 1] as int
        }
    }

    pub open spec fn sequential_prefix_sum(nums: Seq<i32>) -> int {
        Self::prefix_sum(nums, Self::sequential_prefix_len(nums) as int)
    }

    proof fn lemma_sequential_prefix_len_at_break(nums: Seq<i32>, i: int)
        requires
            1 <= i <= nums.len(),
            forall |j: int| 1 <= j < i ==> #[trigger] nums[j] == nums[j - 1] + 1,
            i < nums.len() ==> nums[i] != nums[i - 1] + 1,
        ensures
            Self::sequential_prefix_len(nums) == i,
        decreases i,
    {
        if i == 1 {
            if nums.len() == 1 {
            } else {
                assert(nums[1] != nums[0] + 1);
            }
        } else {
            Self::lemma_sequential_prefix_len_at_break(nums.subrange(1, nums.len() as int), i - 1);
        }
    }

    #[verifier::exec_allows_no_decreases_clause]
    pub fn missing_integer(nums: Vec<i32>) -> (res: i32)
        requires
            1 <= nums.len() <= 50,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 50,
        ensures
            res >= Self::sequential_prefix_sum(nums@),
            !Self::contains(nums@, res),
            forall |x: int| Self::sequential_prefix_sum(nums@) <= x < res ==> #[trigger] Self::contains(nums@, x as i32),
            1 <= res,
    {
        let n = nums.len();

        let mut prefix_sum = nums[0];
        let mut i: usize = 1;
        proof {
            reveal_with_fuel(Solution::prefix_sum, 2);
            assert(Self::prefix_sum(nums@, 0) == 0);
            assert(Self::prefix_sum(nums@, 1) == nums@[0] as int);
            assert(prefix_sum as int == Self::prefix_sum(nums@, i as int));
        }
        while i < n && nums[i] == nums[i - 1] + 1
            invariant
                n == nums.len(),
                1 <= nums.len() <= 50,
                forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 50,
                1 <= i <= n,
                prefix_sum as int == Self::prefix_sum(nums@, i as int),
                1 <= prefix_sum as int <= i as int * 50,
                forall |j: int| 1 <= j < i as int ==> #[trigger] nums[j] == nums[j - 1] + 1,
        {
            prefix_sum += nums[i];
            i += 1;
        }

        proof {
            Self::lemma_sequential_prefix_len_at_break(nums@, i as int);
            assert(Self::sequential_prefix_len(nums@) == i as int);
            assert(Self::sequential_prefix_sum(nums@) == Self::prefix_sum(nums@, i as int));
            assert(prefix_sum as int == Self::sequential_prefix_sum(nums@));
        }

        let mut candidate = prefix_sum;
        let mut found = false;
        while !found
            invariant
                n == nums.len(),
                1 <= nums.len() <= 50,
                forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 50,
                1 <= candidate,
                candidate as int >= Self::sequential_prefix_sum(nums@),
                forall |x: int| Self::sequential_prefix_sum(nums@) <= x < candidate ==> #[trigger] Self::contains(nums@, x as i32),
                found ==> !Self::contains(nums@, candidate),
        {
            let mut exists = false;
            let mut j: usize = 0;
            while j < n && !exists
                invariant
                    n == nums.len(),
                    1 <= nums.len() <= 50,
                    forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 50,
                    0 <= j <= n,
                    exists ==> exists |t: int| 0 <= t < j && nums[t] == candidate,
                    !exists ==> forall |t: int| 0 <= t < j ==> nums[t] != candidate,
            {
                if nums[j] == candidate {
                    exists = true;
                }
                j += 1;
            }

            if !exists {
                assert(j == n);
                assert forall |t: int| 0 <= t < nums.len() implies nums[t] != candidate by {
                    assert(t < j);
                };
                assert(!Self::contains(nums@, candidate));
                found = true;
            } else {
                assert(exists |t: int| 0 <= t < j && (nums@).index(t) == candidate);
                let ghost t = choose |t: int| 0 <= t < j && (nums@).index(t) == candidate;
                assert(0 <= t < nums.len());
                assert((nums@).index(t) == candidate);
                assert(Self::contains(nums@, candidate));
                candidate += 1;
                assert(forall |x: int| Self::sequential_prefix_sum(nums@) <= x < candidate ==> #[trigger] Self::contains(nums@, x as i32)) by {
                    assert forall |x: int| Self::sequential_prefix_sum(nums@) <= x < candidate implies #[trigger] Self::contains(nums@, x as i32) by {
                        if x < candidate - 1 {
                            assert(Self::contains(nums@, x as i32));
                        } else {
                            assert(x == candidate - 1);
                            assert(Self::contains(nums@, (candidate - 1) as i32));
                        }
                    };
                };
            }
        }

        candidate
    }
}

}
