use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_reorder_of<T>(r: Seq<int>, p: Seq<T>, s: Seq<T>) -> bool {
        &&& r.len() == s.len()
        &&& p.len() == s.len()
        &&& forall |i: int| 0 <= i < r.len() ==> 0 <= #[trigger] r[i] < r.len()
        &&& forall |i: int, j: int| 0 <= i < j < r.len() ==> r[i] != r[j]
        &&& p =~= r.map_values(|i: int| s[i])
    }

    pub open spec fn not_average_at(s: Seq<i32>, i: int) -> bool {
        &&& 1 <= i < s.len() - 1
        &&& 2 * (s[i] as int) != (s[i - 1] as int) + (s[i + 1] as int)
    }

    pub fn rearrange_array(nums: Vec<i32>) -> (result: Vec<i32>)
        requires
            3 <= nums.len() <= 100_000,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 100_000,
            forall |i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] != nums[j],
        ensures
            result.len() == nums.len(),
            exists |r: Seq<int>| Self::is_reorder_of(r, result@, nums@),
            forall |i: int| 1 <= i < result.len() - 1 ==> #[trigger] Self::not_average_at(result@, i),
    {
    }
}

}
