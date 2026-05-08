use vstd::prelude::*;
use std::collections::HashMap;

fn main() {}

verus! {

broadcast use vstd::std_specs::hash::group_hash_axioms;

pub struct Solution;

impl Solution {
    pub fn contains_nearby_duplicate(nums: Vec<i32>, k: i32) -> (res: bool) 
        requires
            1 <= nums.len() <= 10_000, 
            forall |i: int| 1 <= i < nums.len() ==> 
                -1_000_000_000 <= #[trigger] nums[i] <= 1_000_000_000,
            0 <= k <= 10_000,
        ensures 
            res == (exists |i: int, j: int| 0 <= i < j < nums.len() && 
                nums[i] == nums[j] && (j - i <= k as int)),
    {
        let mut map: HashMap<i32, usize> = HashMap::new();
        for i in 0..nums.len() 
            invariant
                1 <= nums.len() <= 10_000, 
                forall |idx: int| 1 <= idx < nums.len() ==> 
                    -1_000_000_000 <= #[trigger] nums[idx] <= 1_000_000_000,
                0 <= k <= 10_000,
                forall |a: int, b: int| (0 <= a < b < i && nums[a] == nums[b]) ==> 
                    b - a > k as int,
                forall |v: i32| #[trigger] map@.contains_key(v) ==> 
                    (map@[v] < i && nums[map@[v] as int] == v),
                forall |j: int| 0 <= j < i ==> map@.contains_key(#[trigger] nums[j]),
                forall |v: i32, j: int| (#[trigger] map@.contains_key(v) && 0 <= j < i && #[trigger] nums[j] == v) ==> 
                    j <= map@[v] as int,
        {
            if let Some(prev) = map.get(&nums[i]) {
                proof {
                    assert(map@[nums[i as int]] == *prev);
                    assert(*prev < i);
                }
                if i - *prev <= k as usize {
                    proof {
                        assert(nums[*prev as int] == nums[i as int]);
                        assert(0 <= (*prev as int) < (i as int) < nums@.len() as int);
                        assert((i as int) - (*prev as int) <= k as int);
                    }
                    return true;
                }
                proof {
                    assert forall |a: int, b: int| (0 <= a < b < (i + 1) && nums[a] == nums[b]) 
                        implies b - a > k as int by {
                        if b == i as int {
                            assert(map@.contains_key(nums[i as int]));
                            assert(a <= map@[nums[i as int]] as int);
                        }
                    }
                }
            } else {
                proof {
                    assert(!map@.contains_key(nums[i as int]));
                    assert forall |a: int, b: int| (0 <= a < b < (i + 1) && nums[a] == nums[b]) 
                        implies b - a > k as int by {
                        if b == i as int {
                            assert(map@.contains_key(nums[a]));
                        }
                    }
                }
            }
            map.insert(nums[i], i);
            proof {
                assert forall |v: i32| #[trigger] map@.contains_key(v) implies 
                    (map@[v] < (i + 1) && nums[map@[v] as int] == v) by {
                    if v == nums[i as int] {
                    }
                }
                assert forall |j: int| 0 <= j < (i + 1) implies 
                    map@.contains_key(#[trigger] nums[j]) by {
                }
                assert forall |v: i32, j: int| (#[trigger] map@.contains_key(v) && 0 <= j < (i + 1) && #[trigger] nums[j] == v) 
                    implies j <= map@[v] as int by {
                    if v == nums[i as int] {
                    }
                }
            }
        }
        false
    }
}

}
