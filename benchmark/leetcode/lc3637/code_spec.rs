use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn inc_prefix(nums: Seq<i32>, p: int) -> bool {
        0 < p && p < nums.len()
        && forall|j: int| 0 <= j && j < p ==> #[trigger] nums[j] < nums[j + 1]
    }

    pub open spec fn dec_mid(nums: Seq<i32>, p: int, q: int) -> bool {
        0 < p && p < q && q < nums.len()
        && forall|j: int| p <= j && j < q ==> #[trigger] nums[j] > nums[j + 1]
    }

    pub open spec fn inc_suffix(nums: Seq<i32>, q: int) -> bool {
        0 <= q && q < nums.len() - 1
        && forall|j: int| q <= j && j < nums.len() - 1 ==> #[trigger] nums[j] < nums[j + 1]
    }

    pub open spec fn trionic_at(nums: Seq<i32>, p: int, q: int) -> bool {
        0 < p && p < q && q < nums.len() - 1
        && Self::inc_prefix(nums, p)
        && Self::dec_mid(nums, p, q)
        && Self::inc_suffix(nums, q)
    }

    pub open spec fn has_trionic(nums: Seq<i32>) -> bool {
        exists|p: int, q: int| #[trigger] Self::trionic_at(nums, p, q)
    }

    fn check_prefix_inc(nums: &Vec<i32>, p: usize) -> (result: bool)
        requires
            3 <= nums.len() <= 100,
            0 < p < nums.len(),
            forall|i: int| 0 <= i && i < nums.len() ==> -1000 <= #[trigger] nums[i] <= 1000,
        ensures
            result == Self::inc_prefix(nums@, p as int),
    {
        let mut i: usize = 0;
        while i < p {
            if nums[i] >= nums[i + 1] {
                return false;
            }
            i += 1;
        }
        true
    }

    fn check_mid_dec(nums: &Vec<i32>, p: usize, q: usize) -> (result: bool)
        requires
            3 <= nums.len() <= 100,
            0 < p < q < nums.len(),
            forall|i: int| 0 <= i && i < nums.len() ==> -1000 <= #[trigger] nums[i] <= 1000,
        ensures
            result == Self::dec_mid(nums@, p as int, q as int),
    {
        let mut i: usize = p;
        while i < q {
            if nums[i] <= nums[i + 1] {
                return false;
            }
            i += 1;
        }
        true
    }

    fn check_suffix_inc(nums: &Vec<i32>, q: usize) -> (result: bool)
        requires
            3 <= nums.len() <= 100,
            0 <= q < nums.len() - 1,
            forall|i: int| 0 <= i && i < nums.len() ==> -1000 <= #[trigger] nums[i] <= 1000,
        ensures
            result == Self::inc_suffix(nums@, q as int),
    {
        let n = nums.len();
        let mut i: usize = q;
        while i + 1 < n {
            if nums[i] >= nums[i + 1] {
                return false;
            }
            i += 1;
        }
        true
    }

    fn check_pq(nums: &Vec<i32>, p: usize, q: usize) -> (result: bool)
        requires
            3 <= nums.len() <= 100,
            0 < p < q < nums.len() - 1,
            forall|i: int| 0 <= i && i < nums.len() ==> -1000 <= #[trigger] nums[i] <= 1000,
        ensures
            result == Self::trionic_at(nums@, p as int, q as int),
    {
        let a = Self::check_prefix_inc(nums, p);
        if !a {
            return false;
        }

        let b = Self::check_mid_dec(nums, p, q);
        if !b {
            return false;
        }

        let c = Self::check_suffix_inc(nums, q);
        if !c {
            return false;
        }

        true
    }

    pub fn is_trionic(nums: Vec<i32>) -> (result: bool)
        requires
            3 <= nums.len() <= 100,
            forall|i: int| 0 <= i && i < nums.len() ==> -1000 <= #[trigger] nums[i] <= 1000,
        ensures
            result == Self::has_trionic(nums@),
    {
        let n = nums.len();
        if n < 4 {
            return false;
        }

        let mut p: usize = 1;
        while p + 2 < n {
            let mut q: usize = p + 1;
            while q + 1 < n {
                if Self::check_pq(&nums, p, q) {
                    return true;
                }
                q += 1;
            }
            p += 1;
        }

        false
    }
}

}
