use vstd::prelude::*;
use std::collections::HashSet;

fn main() {}

verus! {

broadcast use vstd::std_specs::hash::group_hash_axioms;

pub struct Solution;

impl Solution {
    pub fn contains_duplicate(nums: Vec<i32>) -> (res: bool) 
        requires
            1 <= nums.len() <= 10_000, 
            forall |i: int| 1 <= i < nums.len() ==> 
                -1_000_000_000 <= #[trigger] nums[i] <= 1_000_000_000,
        ensures 
            res == (exists |i: int, j: int| 0 <= i < j < nums.len() && nums[i] == nums[j]),
    {
        let mut seen = HashSet::new();
        for i in 0..nums.len() 
            invariant
                1 <= nums.len() <= 10_000, 
                forall |k: int| 1 <= k < nums.len() ==> 
                    -1_000_000_000 <= #[trigger] nums[k] <= 1_000_000_000,
                forall |k: int| 0 <= k < i ==> seen@.contains(#[trigger] nums[k]),
                forall |v: i32| seen@.contains(v) ==> exists |k: int| 0 <= k < i && nums[k] == v,
                forall |k: int, m: int| 0 <= k < i && k < m < i ==> nums[k] != nums[m],
        {
            if seen.contains(&nums[i]) {
                proof {
                    let v = nums[i as int];
                    assert(seen@.contains(v));
                    let k = choose |k: int| 0 <= k < i && nums[k] == v;
                    assert(0 <= k < (i as int) < nums@.len() && nums[k] == nums[i as int]);
                }
                return true;
            }
            proof {
                assert forall |k: int, m: int| 0 <= k < (i+1) && k < m < (i+1) implies nums[k] != nums[m] by {
                    if m < i as int {
                    } else {
                        assert(seen@.contains(nums[k]));
                        assert(!seen@.contains(nums[i as int]));
                    }
                }
            }
            seen.insert(nums[i]);
        }
        proof {
            assert(forall |k: int, m: int| 0 <= k < nums.len() && k < m < nums.len() ==> nums[k] != nums[m]);
        }
        false
    }
}

}