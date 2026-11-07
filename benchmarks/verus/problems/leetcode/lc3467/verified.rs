use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_even_count(nums: Seq<i32>, k: int) -> int
    decreases k,
{
    if k <= 0 {
        0
    } else if nums[k - 1] as int % 2 == 0 {
        spec_even_count(nums, k - 1) + 1
    } else {
        spec_even_count(nums, k - 1)
    }
}

proof fn lemma_even_count_bounds(nums: Seq<i32>, k: int)
    requires
        0 <= k <= nums.len(),
    ensures
        0 <= spec_even_count(nums, k) <= k,
    decreases k,
{
    if k <= 0 {
    } else {
        lemma_even_count_bounds(nums, k - 1);
    }
}

impl Solution {
    pub fn transform_array(nums: Vec<i32>) -> (answer: Vec<i32>)
        requires
            1 <= nums.len() <= 100,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
        ensures
            answer.len() == nums.len(),
            forall |i: int| 0 <= i < spec_even_count(nums@, nums.len() as int) ==> #[trigger] answer[i] == 0,
            forall |i: int| spec_even_count(nums@, nums.len() as int) <= i < nums.len() ==> #[trigger] answer[i] == 1,
    {
        let n = nums.len();
        let mut even_count: usize = 0;
        let mut i: usize = 0;
        while i < n
            invariant
                n == nums.len(),
                1 <= n <= 100,
                forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 1000,
                0 <= i <= n,
                even_count as int == spec_even_count(nums@, i as int),
                0 <= even_count <= i,
            decreases n - i,
        {
            proof {
                lemma_even_count_bounds(nums@, (i + 1) as int);
            }
            if (nums[i] as u32) % 2 == 0 {
                even_count += 1;
            }
            i += 1;
        }
        let mut answer: Vec<i32> = vec![0i32; n];
        let mut j: usize = even_count;
        while j < n
            invariant
                n == nums.len(),
                0 <= even_count <= n,
                even_count <= j <= n,
                answer.len() == n,
                even_count as int == spec_even_count(nums@, n as int),
                forall |k: int| 0 <= k < even_count ==> #[trigger] answer[k] == 0i32,
                forall |k: int| even_count as int <= k < j ==> #[trigger] answer[k] == 1i32,
                forall |k: int| j as int <= k < n ==> #[trigger] answer[k] == 0i32,
            decreases n - j,
        {
            answer.set(j, 1);
            j += 1;
        }
        answer
    }
}

} 
