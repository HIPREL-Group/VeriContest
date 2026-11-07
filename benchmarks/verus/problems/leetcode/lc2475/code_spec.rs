use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_triples_k(s: Seq<i32>, i: int, j: int, k: int) -> int
        decreases s.len() - k
    {
        if k >= s.len() { 0 }
        else {
            (if s[i] != s[j] && s[i] != s[k] && s[j] != s[k] { 1int } else { 0int })
            + Self::count_triples_k(s, i, j, k + 1)
        }
    }

    pub open spec fn count_triples_j(s: Seq<i32>, i: int, j: int) -> int
        decreases s.len() - j
    {
        if j >= s.len() { 0 }
        else {
            Self::count_triples_k(s, i, j, j + 1) + Self::count_triples_j(s, i, j + 1)
        }
    }

    pub open spec fn count_triples_i(s: Seq<i32>, i: int) -> int
        decreases s.len() - i
    {
        if i >= s.len() { 0 }
        else {
            Self::count_triples_j(s, i, i + 1) + Self::count_triples_i(s, i + 1)
        }
    }

    pub fn unequal_triplets(nums: Vec<i32>) -> (result: i32)
        requires
            3 <= nums.len() <= 100,
            forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
        ensures
            result as int == Self::count_triples_i(nums@, 0),
    {
        let n = nums.len();
        if n < 3 {
            return 0;
        }
        let mut ans: i32 = 0;
        let mut i: usize = 0;
        while i < n - 2
        {
            let mut j: usize = i + 1;
            while j < n - 1
            {
                let mut k: usize = j + 1;
                while k < n
                {
                    if nums[i] != nums[j] && nums[i] != nums[k] && nums[j] != nums[k] {
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
