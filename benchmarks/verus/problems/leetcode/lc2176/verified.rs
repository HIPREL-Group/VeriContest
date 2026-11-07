use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn is_valid_pair(nums: Seq<i32>, k: int, i: int, j: int) -> bool {
    0 <= i < j < nums.len()
    && nums[i] == nums[j]
    && (i * j) % k == 0
}

pub open spec fn count_inner(nums: Seq<i32>, k: int, i: int, j: int) -> int
    decreases j - i - 1,
{
    if j <= i + 1 {
        0
    } else {
        count_inner(nums, k, i, j - 1)
            + if is_valid_pair(nums, k, i, j - 1) { 1int } else { 0int }
    }
}

pub open spec fn count_all(nums: Seq<i32>, k: int, i: int) -> int
    decreases nums.len() - i,
{
    if i >= nums.len() {
        0
    } else {
        count_all(nums, k, i + 1) + count_inner(nums, k, i, nums.len() as int)
    }
}

proof fn lemma_count_inner_bound(nums: Seq<i32>, k: int, i: int, j: int)
    requires
        0 <= i,
        j <= nums.len(),
    ensures
        0 <= count_inner(nums, k, i, j) <= if j > i + 1 { j - i - 1 } else { 0 },
    decreases j - i - 1,
{
    if j <= i + 1 {
    } else {
        lemma_count_inner_bound(nums, k, i, j - 1);
    }
}

proof fn lemma_count_inner_mono(nums: Seq<i32>, k: int, i: int, j1: int, j2: int)
    requires
        0 <= i,
        j1 <= j2,
        j2 <= nums.len(),
    ensures
        count_inner(nums, k, i, j1) <= count_inner(nums, k, i, j2),
    decreases j2 - j1,
{
    if j1 >= j2 {
    } else {
        lemma_count_inner_mono(nums, k, i, j1, j2 - 1);
        
    }
}

proof fn lemma_count_all_bound(nums: Seq<i32>, k: int, i: int)
    requires
        0 <= i,
        nums.len() <= 100,
    ensures
        0 <= count_all(nums, k, i),
        count_all(nums, k, i) <= if i < nums.len() {
            (nums.len() - i) * nums.len()
        } else {
            0int
        },
    decreases nums.len() - i,
{
    if i >= nums.len() {
    } else {
        lemma_count_all_bound(nums, k, i + 1);
        lemma_count_inner_bound(nums, k, i, nums.len() as int);
        assert(count_inner(nums, k, i, nums.len() as int) <= nums.len() - i - 1);
        assert(count_all(nums, k, i + 1) <= if (i + 1) < nums.len() {
            (nums.len() - (i + 1)) * nums.len()
        } else {
            0int
        });
        assert(count_all(nums, k, i) <= (nums.len() - i - 1) + (nums.len() - (i + 1)) * nums.len()) by {
            
        }
        assert((nums.len() - i - 1) + (nums.len() - (i + 1)) * nums.len() <= (nums.len() - i) * nums.len()) by(nonlinear_arith)
            requires
                0 <= i < nums.len() <= 100,
        {}
    }
}

impl Solution {
    pub fn count_pairs(nums: Vec<i32>, k: i32) -> (res: i32)
        requires
            1 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
            1 <= k <= 100,
        ensures
            res as int == count_all(nums@, k as int, 0),
    {
        let n = nums.len();
        let mut count: i64 = 0;
        let mut i: usize = 0;

        proof {
            lemma_count_all_bound(nums@, k as int, 0);
            assert(count_all(nums@, k as int, 0) <= nums.len() * nums.len());
            assert(nums.len() * nums.len() <= 10000) by(nonlinear_arith)
                requires nums.len() <= 100;
        }

        while i < n
            invariant
                n == nums.len(),
                1 <= nums.len() <= 100,
                forall |idx: int| 0 <= idx < nums.len() ==> 1 <= #[trigger] nums[idx] <= 100,
                1 <= k <= 100,
                0 <= i <= n,
                0 <= count <= 10000,
                count == count_all(nums@, k as int, 0) - count_all(nums@, k as int, i as int),
            decreases n - i,
        {
            let mut j: usize = i + 1;

            proof {
                lemma_count_inner_bound(nums@, k as int, i as int, (i + 1) as int);
            }

            while j < n
                invariant
                    n == nums.len(),
                    1 <= nums.len() <= 100,
                    forall |idx: int| 0 <= idx < nums.len() ==> 1 <= #[trigger] nums[idx] <= 100,
                    1 <= k <= 100,
                    0 <= i < n,
                    i + 1 <= j <= n,
                    0 <= count <= 10000,
                    count == count_all(nums@, k as int, 0) - count_all(nums@, k as int, i as int)
                        + count_inner(nums@, k as int, i as int, j as int),
                decreases n - j,
            {
                proof {
                    
                    
                    lemma_count_inner_bound(nums@, k as int, i as int, (j + 1) as int);
                    lemma_count_all_bound(nums@, k as int, i as int);
                    lemma_count_all_bound(nums@, k as int, (i + 1) as int);
                    
                    lemma_count_inner_mono(nums@, k as int, i as int, (j + 1) as int, nums.len() as int);
                    
                    
                    
                    
                    
                    
                    assert(count_all(nums@, k as int, i as int) == count_all(nums@, k as int, (i + 1) as int) + count_inner(nums@, k as int, i as int, nums.len() as int));
                }

                proof {
                    assert(i * j <= 99 * 99) by(nonlinear_arith)
                        requires 0 <= i < 100, 0 <= j < 100;
                    assert(i * j < 0x8000_0000) by(nonlinear_arith)
                        requires 0 <= i * j <= 9801;
                }
                if nums[i] == nums[j] && ((i * j) as i32) % k == 0 {
                    proof {
                        assert(((i * j) as i32) as int == (i * j) as int);
                        assert(is_valid_pair(nums@, k as int, i as int, j as int));
                    }
                    count = count + 1;
                } else {
                    proof {
                        if nums@[i as int] == nums@[j as int] {
                            assert(((i * j) as i32) as int == (i * j) as int);
                            assert(((i * j) as i32) % k != 0);
                            assert((i * j) % (k as int) != 0);
                        }
                    }
                    assert(!is_valid_pair(nums@, k as int, i as int, j as int));
                }

                
                assert(count == count_all(nums@, k as int, 0) - count_all(nums@, k as int, i as int)
                    + count_inner(nums@, k as int, i as int, (j + 1) as int));

                proof {
                    
                    lemma_count_all_bound(nums@, k as int, 0);
                    lemma_count_all_bound(nums@, k as int, (i + 1) as int);
                    assert(count_inner(nums@, k as int, i as int, (j + 1) as int) <= count_inner(nums@, k as int, i as int, nums.len() as int));
                    assert(count_all(nums@, k as int, (i + 1) as int) >= 0);
                    assert(count_all(nums@, k as int, 0) <= nums.len() * nums.len());
                    assert(nums.len() * nums.len() <= 10000) by(nonlinear_arith)
                        requires nums.len() <= 100;
                }

                j += 1;
            }

            
            assert(count == count_all(nums@, k as int, 0) - count_all(nums@, k as int, i as int)
                + count_inner(nums@, k as int, i as int, n as int));
            
            
            assert(count == count_all(nums@, k as int, 0) - count_all(nums@, k as int, (i + 1) as int));

            proof {
                lemma_count_all_bound(nums@, k as int, (i + 1) as int);
            }

            i += 1;
        }

        
        assert(count_all(nums@, k as int, n as int) == 0int);
        assert(count == count_all(nums@, k as int, 0));

        count as i32
    }
}

} 
