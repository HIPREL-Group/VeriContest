use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn sorted(nums: Seq<i64>) -> bool {
    forall|i: int| 0 <= i < nums.len() - 1 ==> #[trigger] nums[i] <= nums[i + 1]
}

pub open spec fn gap(nums: Seq<i64>, i: int) -> int
    recommends 0 <= i < nums.len() - 1,
{
    nums[i + 1] as int - nums[i] as int
}

pub open spec fn lifted_index(i: int, miss: int) -> int {
    if i < miss { i } else { i + 1 }
}

pub open spec fn fits_with_missing(nums: Seq<i64>, start: int, d: int, miss: int) -> bool {
    &&& d >= 0
    &&& 0 <= miss <= nums.len()
    &&& forall|i: int| 0 <= i < nums.len() ==> #[trigger] nums[i] as int == start + lifted_index(i, miss) * d
}

pub open spec fn is_candidate(nums: Seq<i64>, x: int) -> bool {
    exists|start: int, d: int, miss: int| {
        &&& fits_with_missing(nums, start, d, miss)
        &&& x == start + miss * d
    }
}

pub open spec fn min_gap(nums: Seq<i64>, end: int) -> int
    decreases end,
{
    if end <= 2 {
        gap(nums, 0)
    } else {
        let prev = min_gap(nums, end - 1);
        let cur = gap(nums, end - 2);
        if prev <= cur { prev } else { cur }
    }
}

pub open spec fn gap_pattern(nums: Seq<i64>, d: int, miss: int) -> bool {
    &&& nums.len() >= 1
    &&& d >= 0
    &&& 0 <= miss <= nums.len()
    &&& forall|i: int| 0 <= i < nums.len() - 1 ==> #[trigger] gap(nums, i) == if i + 1 == miss { 2 * d } else { d }
}

pub open spec fn candidate_start(nums: Seq<i64>, d: int, miss: int) -> int {
    if miss == 0 { nums[0] as int - d } else { nums[0] as int }
}

pub open spec fn candidate_value_from_pattern(nums: Seq<i64>, d: int, miss: int) -> int {
    candidate_start(nums, d, miss) + miss * d
}

impl Solution {
    pub fn arithmetic_progression_insertions(nums: Vec<i64>) -> (result: Option<Vec<i64>>)
        requires
            1 <= nums.len() <= 100_000,
            sorted(nums@),
            forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100_000_000,
        ensures
            result == None::<Vec<i64>> ==> nums.len() == 1 && forall|x: int| is_candidate(nums@, x),
            result != None::<Vec<i64>> ==> nums.len() >= 2,
            result != None::<Vec<i64>> ==> forall|i: int, j: int|
                0 <= i < j < result->0.len() ==> #[trigger] result->0[i] < #[trigger] result->0[j],
            result != None::<Vec<i64>> ==> forall|i: int|
                0 <= i < result->0.len() ==> is_candidate(nums@, #[trigger] result->0[i] as int),
            result != None::<Vec<i64>> ==> forall|x: int|
                is_candidate(nums@, x) ==> exists|i: int| 0 <= i < result->0.len() && result->0[i] as int == x,
    {
    }
}

}
