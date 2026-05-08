use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn appears_in(s: Seq<i32>, val: i32) -> bool {
        exists |j: int| 0 <= j < s.len() && #[trigger] s[j] == val
    }

    pub open spec fn appears_twice(s: Seq<i32>, val: i32) -> bool {
        exists |j1: int, j2: int| 0 <= j1 < j2 < s.len()
            && #[trigger] s[j1] == val && #[trigger] s[j2] == val
    }

    pub fn find_error_nums(nums: Vec<i32>) -> (result: Vec<i32>)
        requires
            2 <= nums.len() <= 10_000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= nums.len(),
            exists |d: int| 1 <= d <= nums.len() && #[trigger] Self::appears_twice(nums@, d as i32),
            exists |m: int| 1 <= m <= nums.len() && !#[trigger] Self::appears_in(nums@, m as i32),
            forall |v1: i32, v2: i32|
                Self::appears_twice(nums@, v1) && Self::appears_twice(nums@, v2) ==> v1 == v2,
            forall |v1: int, v2: int|
                1 <= v1 <= nums.len() && 1 <= v2 <= nums.len()
                && !#[trigger] Self::appears_in(nums@, v1 as i32) && !#[trigger] Self::appears_in(nums@, v2 as i32)
                ==> v1 == v2,
        ensures
            result.len() == 2,
            1 <= result[0] <= nums.len() as i32,
            1 <= result[1] <= nums.len() as i32,
            result[0] != result[1],
            Self::appears_twice(nums@, result[0]),
            !Self::appears_in(nums@, result[1]),
    {
        let n = nums.len();
        let mut dup: i32 = 1;
        let mut miss: i32 = 1;
        let mut found_dup: bool = false;
        let mut found_miss: bool = false;
        let mut k: usize = 1;

        while k <= n {
            let mut seen_first: bool = false;
            let mut first_idx: usize = 0;
            let mut seen_second: bool = false;
            let mut i: usize = 0;

            while i < n {
                if nums[i] == k as i32 {
                    if seen_first {
                        seen_second = true;
                    } else {
                        first_idx = i;
                    }
                    seen_first = true;
                }
                i = i + 1;
            }

            if seen_second && !found_dup {
                dup = k as i32;
                found_dup = true;
            }
            if !seen_first && !found_miss {
                miss = k as i32;
                found_miss = true;
            }

            k = k + 1;
        }

        let mut result = Vec::new();
        result.push(dup);
        result.push(miss);
        result
    }
}

}
