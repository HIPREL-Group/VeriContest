use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;



pub open spec fn split_cost(nums: Seq<i32>, i: int, j: int) -> int {
    nums[0] as int + nums[i] as int + nums[j] as int
}


pub open spec fn spec_minimum_cost(nums: Seq<i32>) -> int {
    
    
    
    
    nums[0] as int + spec_two_smallest_sum(nums, nums.len() as int)
}



pub open spec fn spec_min1(nums: Seq<i32>, k: int) -> int
    decreases k,
{
    if k <= 1 {
        51  
    } else if (nums[k - 1] as int) < spec_min1(nums, k - 1) {
        nums[k - 1] as int
    } else {
        spec_min1(nums, k - 1)
    }
}

pub open spec fn spec_min2(nums: Seq<i32>, k: int) -> int
    decreases k,
{
    if k <= 1 {
        51
    } else if (nums[k - 1] as int) < spec_min1(nums, k - 1) {
        
        spec_min1(nums, k - 1)
    } else if (nums[k - 1] as int) < spec_min2(nums, k - 1) {
        nums[k - 1] as int
    } else {
        spec_min2(nums, k - 1)
    }
}

pub open spec fn spec_two_smallest_sum(nums: Seq<i32>, k: int) -> int {
    spec_min1(nums, k) + spec_min2(nums, k)
}


proof fn lemma_min1_le_min2(nums: Seq<i32>, k: int)
    requires
        0 <= k <= nums.len() as int,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 50,
    ensures
        spec_min1(nums, k) <= spec_min2(nums, k),
    decreases k,
{
    if k <= 1 {
    } else {
        lemma_min1_le_min2(nums, k - 1);
    }
}


proof fn lemma_min1_bounds(nums: Seq<i32>, k: int)
    requires
        0 <= k <= nums.len() as int,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 50,
    ensures
        1 <= spec_min1(nums, k) <= 51,
        k >= 2 ==> 1 <= spec_min1(nums, k) <= 50,
    decreases k,
{
    if k <= 1 {
    } else {
        lemma_min1_bounds(nums, k - 1);
    }
}


proof fn lemma_min2_bounds(nums: Seq<i32>, k: int)
    requires
        0 <= k <= nums.len() as int,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 50,
    ensures
        1 <= spec_min2(nums, k) <= 51,
        k >= 3 ==> 1 <= spec_min2(nums, k) <= 50,
    decreases k,
{
    if k <= 1 {
    } else {
        lemma_min2_bounds(nums, k - 1);
        lemma_min1_bounds(nums, k - 1);
    }
}


proof fn lemma_min1_is_min(nums: Seq<i32>, k: int)
    requires
        0 <= k <= nums.len() as int,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 50,
    ensures
        forall |j: int| 1 <= j < k ==> spec_min1(nums, k) <= #[trigger] (nums[j] as int),
    decreases k,
{
    if k <= 1 {
    } else {
        lemma_min1_is_min(nums, k - 1);
    }
}


proof fn lemma_min1_exists(nums: Seq<i32>, k: int)
    requires
        2 <= k <= nums.len() as int,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 50,
    ensures
        exists |j: int| 1 <= j < k && spec_min1(nums, k) == #[trigger] (nums[j] as int),
    decreases k,
{
    if k <= 2 {
        
        
        
        assert(spec_min1(nums, 1) == 51);
        assert(nums[1] as int <= 50);
        assert((nums[1] as int) < spec_min1(nums, 1));
        assert(spec_min1(nums, 2) == nums[1] as int);
    } else {
        lemma_min1_exists(nums, k - 1);
    }
}


proof fn lemma_two_smallest_optimal(nums: Seq<i32>, k: int)
    requires
        0 <= k <= nums.len() as int,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 50,
    ensures
        forall |i: int, j: int|
            1 <= i < j < k ==>
            spec_min1(nums, k) + spec_min2(nums, k) <= (#[trigger] nums[i] as int) + (#[trigger] nums[j] as int),
    decreases k,
{
    if k <= 2 {
    } else {
        lemma_two_smallest_optimal(nums, k - 1);
        lemma_min1_is_min(nums, k - 1);
        lemma_min1_le_min2(nums, k - 1);
        lemma_min1_is_min(nums, k);
    }
}



proof fn lemma_two_smallest_achievable(nums: Seq<i32>, k: int)
    requires
        3 <= k <= nums.len() as int,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 50,
    ensures
        exists |i: int, j: int|
            1 <= i < j < k
            && spec_min1(nums, k) + spec_min2(nums, k) == (#[trigger] nums[i] as int) + (#[trigger] nums[j] as int),
    decreases k,
{
    if k == 3 {
        
        
        assert(spec_min1(nums, 1) == 51);
        assert(spec_min2(nums, 1) == 51);
        assert((nums[1] as int) < 51);
        assert(spec_min1(nums, 2) == nums[1] as int);
        assert(spec_min2(nums, 2) == 51);
        
        if (nums[2] as int) < (nums[1] as int) {
            assert(spec_min1(nums, 3) == nums[2] as int);
            assert(spec_min2(nums, 3) == nums[1] as int);
        } else {
            assert(spec_min1(nums, 3) == nums[1] as int);
            assert((nums[2] as int) < spec_min2(nums, 2));
            assert(spec_min2(nums, 3) == nums[2] as int);
        }
        assert(spec_min1(nums, 3) + spec_min2(nums, 3) == (nums[1] as int) + (nums[2] as int));
    } else {
        lemma_two_smallest_achievable(nums, k - 1);
        lemma_min1_exists(nums, k - 1);
        
        
        
        
        
        
        
        
        
        
        if (nums[k - 1] as int) < spec_min1(nums, k - 1) {
            
            let j0 = choose |j: int| 1 <= j < k - 1 && spec_min1(nums, k - 1) == #[trigger] (nums[j] as int);
            assert(1 <= j0 < k - 1);
            
            
            assert(spec_min1(nums, k) + spec_min2(nums, k) == (nums[k - 1] as int) + (nums[j0] as int));
            if j0 < k - 1 {
                assert(1 <= j0 && j0 < k - 1 && k - 1 < k);
            }
        } else if (nums[k - 1] as int) < spec_min2(nums, k - 1) {
            let j0 = choose |j: int| 1 <= j < k - 1 && spec_min1(nums, k - 1) == #[trigger] (nums[j] as int);
            assert(1 <= j0 < k - 1);
            assert(spec_min1(nums, k) + spec_min2(nums, k) == (nums[j0] as int) + (nums[k - 1] as int));
        } else {
            
        }
    }
}

impl Solution {
    pub fn minimum_cost(nums: Vec<i32>) -> (result: i32)
        requires
            3 <= nums.len() <= 50,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 50,
        ensures
            
            result as int == spec_minimum_cost(nums@),
            
            exists |i: int, j: int|
                1 <= i < j < nums.len()
                && result as int == split_cost(nums@, i, j),
            
            forall |i: int, j: int|
                1 <= i < j < nums.len()
                ==> result as int <= split_cost(nums@, i, j),
    {
        let n = nums.len();
        let mut min1: i32 = 51;
        let mut min2: i32 = 51;
        let mut i: usize = 1;
        while i < n
            invariant
                n == nums.len(),
                3 <= n <= 50,
                1 <= i <= n,
                forall |j: int| 0 <= j < nums.len() ==> 1 <= #[trigger] nums[j] <= 50,
                min1 as int == spec_min1(nums@, i as int),
                min2 as int == spec_min2(nums@, i as int),
                1 <= min1 <= 51,
                1 <= min2 <= 51,
                min1 <= min2,
            decreases n - i,
        {
            proof {
                lemma_min1_bounds(nums@, (i + 1) as int);
                lemma_min2_bounds(nums@, (i + 1) as int);
                lemma_min1_le_min2(nums@, (i + 1) as int);
            }
            if nums[i] < min1 {
                min2 = min1;
                min1 = nums[i];
            } else if nums[i] < min2 {
                min2 = nums[i];
            }
            i = i + 1;
        }
        proof {
            lemma_two_smallest_optimal(nums@, n as int);
            lemma_two_smallest_achievable(nums@, n as int);
            
            assert forall |i: int, j: int|
                1 <= i < j < nums.len()
            implies
                (nums[0] as int + min1 as int + min2 as int) <= split_cost(nums@, i, j)
            by {
                assert(spec_min1(nums@, n as int) + spec_min2(nums@, n as int) <= (nums[i] as int) + (nums[j] as int));
            }
            
            let (wi, wj) = choose |i: int, j: int|
                1 <= i < j < n
                && spec_min1(nums@, n as int) + spec_min2(nums@, n as int) == (#[trigger] nums[i] as int) + (#[trigger] nums[j] as int);
            assert(1 <= wi < wj < nums.len());
            assert((nums[0] as int + min1 as int + min2 as int) == split_cost(nums@, wi, wj));
        }
        nums[0] + min1 + min2
    }
}

} 
