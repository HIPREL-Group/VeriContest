use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;


pub open spec fn spec_max_ops(nums: Seq<i32>, target: int, k: int) -> int
    decreases (nums.len() as int) - 2 * k,
{
    if 2 * k + 1 >= nums.len() {
        0
    } else if (nums[2 * k] as int) + (nums[2 * k + 1] as int) == target {
        1 + spec_max_ops(nums, target, k + 1)
    } else {
        0
    }
}

proof fn lemma_max_ops_bounds(nums: Seq<i32>, target: int, k: int)
    requires
        0 <= k,
        2 * k <= nums.len(),
    ensures
        0 <= spec_max_ops(nums, target, k),
        spec_max_ops(nums, target, k) <= (nums.len() as int - 2 * k) / 2,
    decreases (nums.len() as int) - 2 * k,
{
    if 2 * k + 1 >= nums.len() {
    } else if (nums[2 * k] as int) + (nums[2 * k + 1] as int) == target {
        lemma_max_ops_bounds(nums, target, k + 1);
    } else {
    }
}


proof fn lemma_max_ops_all_match(nums: Seq<i32>, target: int, k: int)
    requires
        0 <= k,
        2 * k <= nums.len(),
    ensures
        forall |j: int| k <= j < k + spec_max_ops(nums, target, k)
            ==> (#[trigger] nums[2 * j] as int) + (nums[2 * j + 1] as int) == target,
    decreases (nums.len() as int) - 2 * k,
{
    if 2 * k + 1 >= nums.len() {
    } else if (nums[2 * k] as int) + (nums[2 * k + 1] as int) == target {
        lemma_max_ops_all_match(nums, target, k + 1);
    } else {
    }
}



proof fn lemma_max_ops_split(nums: Seq<i32>, target: int, k0: int, k1: int)
    requires
        0 <= k0 <= k1,
        2 * k1 <= nums.len(),
        forall |j: int| k0 <= j < k1
            ==> (#[trigger] nums[2 * j] as int) + (nums[2 * j + 1] as int) == target,
    ensures
        spec_max_ops(nums, target, k0) == (k1 - k0) + spec_max_ops(nums, target, k1),
    decreases k1 - k0,
{
    if k0 == k1 {
    } else {
        assert((nums[2 * k0] as int) + (nums[2 * k0 + 1] as int) == target);
        lemma_max_ops_split(nums, target, k0 + 1, k1);
    }
}

impl Solution {
    pub fn max_operations(nums: Vec<i32>) -> (count: i32)
        requires
            2 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
        ensures
            count as int == spec_max_ops(nums@, nums[0] as int + nums[1] as int, 0),
            count >= 1,
            
            forall |k: int| 0 <= k < count
                ==> (#[trigger] nums[2 * k] as int) + (nums[2 * k + 1] as int) == nums[0] as int + nums[1] as int,
    {
        let n = nums.len();
        let score: i32 = nums[0] + nums[1];
        let ghost target: int = nums[0] as int + nums[1] as int;
        let mut count: i32 = 0;
        let mut i: usize = 0;
        let mut matched: bool = true;

        while i + 1 < n && matched
            invariant
                n == nums.len(),
                2 <= n <= 100,
                forall |j: int| 0 <= j < n ==> 1 <= #[trigger] nums[j] <= 1000,
                score as int == target,
                target == nums[0] as int + nums[1] as int,
                2 <= score <= 2000,
                0 <= count <= 50,
                i == 2 * count as usize,
                0 <= i <= n,
                forall |k: int| 0 <= k < count as int
                    ==> (#[trigger] nums[2 * k] as int) + (nums[2 * k + 1] as int) == target,
                !matched ==> spec_max_ops(nums@, target, count as int) == 0,
            decreases n - i, if matched { 1int } else { 0int },
        {
            if nums[i] + nums[i + 1] == score {
                count = count + 1;
                i = i + 2;
            } else {
                matched = false;
            }
        }
        proof {
            if matched {
                
                assert(2 * (count as int) + 1 >= nums@.len());
            }
            assert(spec_max_ops(nums@, target, count as int) == 0);
            lemma_max_ops_split(nums@, target, 0, count as int);
            lemma_max_ops_all_match(nums@, target, 0);
            
            assert((nums@[0] as int) + (nums@[1] as int) == target);
            assert(2 * 0 + 1 < nums@.len() as int);
            
            lemma_max_ops_bounds(nums@, target, 1);
            assert(spec_max_ops(nums@, target, 0) >= 1);
            assert(count >= 1);
        }
        count
    }
}

} 
