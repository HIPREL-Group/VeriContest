use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn is_good_pair(nums: Seq<i32>, i: int, j: int) -> bool {
    0 <= i < j < nums.len()
    && nums[i] == nums[j]
}

pub open spec fn count_inner(nums: Seq<i32>, i: int, j: int) -> int
    decreases j - i - 1,
{
    if j <= i + 1 {
        0
    } else {
        count_inner(nums, i, j - 1)
            + if is_good_pair(nums, i, j - 1) { 1int } else { 0int }
    }
}

pub open spec fn count_all(nums: Seq<i32>, i: int) -> int
    decreases nums.len() - i,
{
    if i >= nums.len() {
        0
    } else {
        count_all(nums, i + 1) + count_inner(nums, i, nums.len() as int)
    }
}

proof fn lemma_count_inner_bound(nums: Seq<i32>, i: int, j: int)
    requires
        0 <= i,
        j <= nums.len(),
    ensures
        0 <= count_inner(nums, i, j) <= if j > i + 1 { j - i - 1 } else { 0 },
    decreases j - i - 1,
{
    if j <= i + 1 {
    } else {
        lemma_count_inner_bound(nums, i, j - 1);
    }
}

proof fn lemma_count_inner_mono(nums: Seq<i32>, i: int, j1: int, j2: int)
    requires
        0 <= i,
        j1 <= j2,
        j2 <= nums.len(),
    ensures
        count_inner(nums, i, j1) <= count_inner(nums, i, j2),
    decreases j2 - j1,
{
    if j1 >= j2 {
    } else {
        lemma_count_inner_mono(nums, i, j1, j2 - 1);
    }
}

proof fn lemma_count_all_bound(nums: Seq<i32>, i: int)
    requires
        0 <= i,
        nums.len() <= 100,
    ensures
        0 <= count_all(nums, i),
        count_all(nums, i) <= if i < nums.len() {
            (nums.len() - i) * nums.len()
        } else {
            0int
        },
    decreases nums.len() - i,
{
    if i >= nums.len() {
    } else {
        lemma_count_all_bound(nums, i + 1);
        lemma_count_inner_bound(nums, i, nums.len() as int);
        assert(count_inner(nums, i, nums.len() as int) <= nums.len() - i - 1);
        assert(count_all(nums, i + 1) <= if (i + 1) < nums.len() {
            (nums.len() - (i + 1)) * nums.len()
        } else {
            0int
        });
        assert((nums.len() - i - 1) + (nums.len() - (i + 1)) * nums.len() <= (nums.len() - i) * nums.len()) by(nonlinear_arith)
            requires
                0 <= i < nums.len() <= 100,
        {}
    }
}

impl Solution {
    pub fn num_identical_pairs(nums: Vec<i32>) -> (res: i32)
        requires
            1 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
        ensures
            res as int == count_all(nums@, 0),
    {
        let n = nums.len();
        let mut count: i64 = 0;
        let mut i: usize = 0;

        proof {
            lemma_count_all_bound(nums@, 0);
            assert(count_all(nums@, 0) <= nums.len() * nums.len());
            assert(nums.len() * nums.len() <= 10000) by(nonlinear_arith)
                requires nums.len() <= 100;
        }

        while i < n
            invariant
                n == nums.len(),
                1 <= nums.len() <= 100,
                forall |idx: int| 0 <= idx < nums.len() ==> 1 <= #[trigger] nums[idx] <= 100,
                0 <= i <= n,
                0 <= count <= 10000,
                count == count_all(nums@, 0) - count_all(nums@, i as int),
            decreases n - i,
        {
            let mut j: usize = i + 1;

            proof {
                lemma_count_inner_bound(nums@, i as int, (i + 1) as int);
            }

            while j < n
                invariant
                    n == nums.len(),
                    1 <= nums.len() <= 100,
                    forall |idx: int| 0 <= idx < nums.len() ==> 1 <= #[trigger] nums[idx] <= 100,
                    0 <= i < n,
                    i + 1 <= j <= n,
                    0 <= count <= 10000,
                    count == count_all(nums@, 0) - count_all(nums@, i as int)
                        + count_inner(nums@, i as int, j as int),
                decreases n - j,
            {
                proof {
                    lemma_count_inner_bound(nums@, i as int, (j + 1) as int);
                    lemma_count_all_bound(nums@, i as int);
                    lemma_count_all_bound(nums@, (i + 1) as int);
                    lemma_count_inner_mono(nums@, i as int, (j + 1) as int, nums.len() as int);
                    assert(count_all(nums@, i as int) == count_all(nums@, (i + 1) as int) + count_inner(nums@, i as int, nums.len() as int));
                }

                if nums[i] == nums[j] {
                    proof {
                        assert(is_good_pair(nums@, i as int, j as int));
                    }
                    count = count + 1;
                } else {
                    assert(!is_good_pair(nums@, i as int, j as int));
                }

                assert(count == count_all(nums@, 0) - count_all(nums@, i as int)
                    + count_inner(nums@, i as int, (j + 1) as int));

                proof {
                    lemma_count_all_bound(nums@, 0);
                    lemma_count_all_bound(nums@, (i + 1) as int);
                    assert(count_inner(nums@, i as int, (j + 1) as int) <= count_inner(nums@, i as int, nums.len() as int));
                    assert(count_all(nums@, (i + 1) as int) >= 0);
                    assert(count_all(nums@, 0) <= nums.len() * nums.len());
                    assert(nums.len() * nums.len() <= 10000) by(nonlinear_arith)
                        requires nums.len() <= 100;
                }

                j += 1;
            }

            assert(count == count_all(nums@, 0) - count_all(nums@, i as int)
                + count_inner(nums@, i as int, n as int));
            assert(count == count_all(nums@, 0) - count_all(nums@, (i + 1) as int));

            proof {
                lemma_count_all_bound(nums@, (i + 1) as int);
            }

            i += 1;
        }

        assert(count_all(nums@, n as int) == 0int);
        assert(count == count_all(nums@, 0));

        count as i32
    }
}

} 
