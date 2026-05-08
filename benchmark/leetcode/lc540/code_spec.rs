use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_occurrences(s: Seq<i32>, value: i32) -> nat
        decreases s.len()
    {
        if s.len() == 0 {
            0
        } else {
            Self::count_occurrences(s.drop_last(), value) +
                if s.last() == value { 1 as nat } else { 0 as nat }
        }
    }

    pub fn single_non_duplicate(nums: Vec<i32>) -> (res: i32)
        requires
            1 <= nums.len() <= 100_000,
            nums.len() % 2 == 1,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 100_000,
            forall |i: int, j: int| 0 <= i < j < nums.len() ==> #[trigger] nums[i] <= #[trigger] nums[j],
            exists |single: i32| {
                &&& Self::count_occurrences(nums@, single) == 1
                &&& forall |v: i32| v != single && (exists |i: int| 0 <= i < nums@.len() && nums@[i] == v)
                        ==> #[trigger] Self::count_occurrences(nums@, v) == 2
            },
        ensures
            Self::count_occurrences(nums@, res) == 1,
    {
        let n = nums.len();
        let mut i: usize = 0;
        while i + 1 < n
        {
            if nums[i] != nums[i + 1] {
                let result = nums[i];
                return result;
            }
            i = i + 2;
        }
        nums[i]
    }
}

}