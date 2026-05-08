use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_perm(nums: Seq<i32>) -> bool {
        let n = nums.len();
        &&& 2 <= n <= 50
        &&& forall |i: int| 0 <= i < n ==> 1 <= #[trigger] nums[i] <= n
        &&& forall |i: int, j: int| 0 <= i < j < n ==> nums[i] != nums[j]
    }

    pub open spec fn is_pos_1(nums: Seq<i32>, i: int) -> bool {
        0 <= i < nums.len() && nums[i] == 1
    }

    pub open spec fn is_pos_n(nums: Seq<i32>, i: int) -> bool {
        0 <= i < nums.len() && nums[i] == nums.len() as i32
    }

    pub open spec fn semi_ordered_swaps(nums: Seq<i32>) -> int
        recommends
            Self::is_perm(nums),
            exists |i: int| Self::is_pos_1(nums, i),
            exists |i: int| Self::is_pos_n(nums, i),
    {
        let i1 = choose |i: int| Self::is_pos_1(nums, i);
        let inx = choose |i: int| Self::is_pos_n(nums, i);
        i1 + (nums.len() - 1 - inx) - if i1 > inx { 1int } else { 0int }
    }

    pub fn semi_ordered_permutation(nums: Vec<i32>) -> (result: i32)
        requires
            Self::is_perm(nums@),
            exists |i: int| Self::is_pos_1(nums@, i),
            exists |i: int| Self::is_pos_n(nums@, i),
        ensures
            result as int == Self::semi_ordered_swaps(nums@),
            0 <= result,
            result <= 2 * nums.len(),
    {
    }
}

}
