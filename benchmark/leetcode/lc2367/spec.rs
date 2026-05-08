use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_triplets_k(s: Seq<i32>, diff: int, i: int, j: int, k: int) -> int
        decreases s.len() - k
    {
        if k >= s.len() { 0 }
        else {
            (if s[j] as int - s[i] as int == diff && s[k] as int - s[j] as int == diff { 1int } else { 0int })
            + Self::count_triplets_k(s, diff, i, j, k + 1)
        }
    }

    pub open spec fn count_triplets_j(s: Seq<i32>, diff: int, i: int, j: int) -> int
        decreases s.len() - j
    {
        if j >= s.len() { 0 }
        else {
            Self::count_triplets_k(s, diff, i, j, j + 1)
            + Self::count_triplets_j(s, diff, i, j + 1)
        }
    }

    pub open spec fn count_triplets(s: Seq<i32>, diff: int, i: int) -> int
        decreases s.len() - i
    {
        if i >= s.len() { 0 }
        else {
            Self::count_triplets_j(s, diff, i, i + 1)
            + Self::count_triplets(s, diff, i + 1)
        }
    }

    pub fn arithmetic_triplets(nums: Vec<i32>, diff: i32) -> (result: i32)
        requires
            3 <= nums.len() <= 200,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 200,
            1 <= diff <= 50,
            forall |i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] < nums[j],
        ensures
            result as int == Self::count_triplets(nums@, diff as int, 0),
    {
    }
}

}
