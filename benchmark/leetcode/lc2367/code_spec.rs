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
        let mut ans: i32 = 0;
        let mut i: usize = 0;
        while i < nums.len() {
            let mut j: usize = i + 1;
            while j < nums.len() {
                let mut k: usize = j + 1;
                while k < nums.len() {
                    if (nums[j] as i64 - nums[i] as i64) == diff as i64
                        && (nums[k] as i64 - nums[j] as i64) == diff as i64 {
                        ans = ans + 1;
                    }
                    k = k + 1;
                }
                j = j + 1;
            }
            i = i + 1;
        }
        ans
    }
}

}
