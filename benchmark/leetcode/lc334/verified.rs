use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn no_triplet_prefix(nums: Seq<i32>, n: int) -> bool {
        forall |a: int, b: int, c: int| #![trigger nums[a], nums[b], nums[c]]
            0 <= a < b < c < n ==> !(nums[a] < nums[b] && nums[b] < nums[c])
    }

    proof fn extend_no_triplet(nums: Seq<i32>, i: int, threshold: i32)
        requires
            0 <= i < nums.len() as int,
            nums[i] == threshold,
            Self::no_triplet_prefix(nums, i),
            forall |a: int, b: int| #![trigger nums[a], nums[b]]
                0 <= a < b < i && nums[a] < nums[b] ==> threshold <= nums[b],
        ensures
            Self::no_triplet_prefix(nums, i + 1),
    {
        assert forall |a: int, b: int, c: int|
            0 <= a < b < c < i + 1
            implies !(nums[a] < nums[b] && nums[b] < nums[c]) by {
            if c < i {
                
            } else {
                
                
                if nums[a] < nums[b] {
                    assert(threshold <= nums[b]);
                    assert(nums[i] == threshold);
                }
            }
        };
    }

    pub fn increasing_triplet(nums: Vec<i32>) -> (res: bool)
        requires
            1 <= nums.len() <= 500_000,
        ensures
            res == (exists |a: int, b: int, c: int| 0 <= a < b < c < nums.len() && nums[a] < nums[b] && nums[b] < nums[c]),
    {
        let mut first: i32 = i32::MAX;
        let mut second: i32 = i32::MAX;

        let ghost mut first_idx: int = 0;
        let ghost mut pair_a: int = 0;
        let ghost mut pair_b: int = 0;

        let mut i: usize = 0;

        while i < nums.len()
            invariant
                0 <= i <= nums.len(),
                1 <= nums.len() <= 500_000,
                first <= second,
                forall |a: int| 0 <= a < i ==> first <= #[trigger] nums[a],
                first < i32::MAX ==> (0 <= first_idx < i && nums[first_idx] == first),
                forall |a: int, b: int| #![trigger nums[a], nums[b]]
                    0 <= a < b < i && nums[a] < nums[b] ==> second <= nums[b],
                second < i32::MAX ==> (0 <= pair_a < pair_b < i && nums[pair_a] < nums[pair_b] && nums[pair_b] == second),
                Self::no_triplet_prefix(nums@, i as int),
            decreases nums.len() - i,
        {
            let n = nums[i];
            let ghost old_first = first;
            let ghost old_second = second;

            if n <= first {
                proof { first_idx = i as int; }
                first = n;
            } else if n <= second {
                proof {
                    pair_a = first_idx;
                    pair_b = i as int;
                }
                second = n;
            } else {
                proof {
                    assert(second < i32::MAX);
                    assert(nums[pair_a] < nums[pair_b] && nums[pair_b] == second && second < n);
                }
                return true;
            }

            proof {
                
                
                assert(first <= i32::MAX);

                
                if first < i32::MAX {
                    assert(first_idx <= i as int) by {
                        
                    };
                    assert(nums@[first_idx] == first);  
                }

                
                if second < i32::MAX {
                    assert(pair_b <= i as int);                   
                    assert(nums@[pair_b] == second);              
                    assert(nums@[pair_a] < nums@[pair_b]) by {
                        
                        
                    };
                }

                
                assert(n <= old_second) by { assert(old_first <= old_second); };

                
                assert forall |a: int, b: int| #![trigger nums@[a], nums@[b]]
                    0 <= a < b < i as int && nums@[a] < nums@[b]
                    implies n <= nums@[b] by {
                    assert(old_second <= nums@[b]);
                };

                
                Self::extend_no_triplet(nums@, i as int, n);
            }

            i = i + 1;
        }

        false
    }
}

}
