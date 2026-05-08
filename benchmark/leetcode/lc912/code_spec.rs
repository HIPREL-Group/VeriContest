use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn sorted(s: Seq<i32>) -> bool {
        forall|i: int, j: int| 0 <= i <= j < s.len() ==> s[i] <= s[j]
    }

    pub open spec fn count_occ(s: Seq<i32>, val: i32) -> int
        decreases s.len(),
    {
        if s.len() == 0 { 0 }
        else {
            (if s.last() == val { 1int } else { 0int })
                + Self::count_occ(s.drop_last(), val)
        }
    }

    pub open spec fn is_perm(a: Seq<i32>, b: Seq<i32>) -> bool {
        a.len() == b.len() && forall|v: i32| Self::count_occ(a, v) == Self::count_occ(b, v)
    }

    fn ms_merge(a: &Vec<i32>, b: &Vec<i32>) -> (result: Vec<i32>) {
        let mut result: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        let mut j: usize = 0;
        while i < a.len() || j < b.len() {
            if i < a.len() && (j >= b.len() || a[i] <= b[j]) {
                result.push(a[i]);
                i = i + 1;
            } else {
                result.push(b[j]);
                j = j + 1;
            }
        }
        result
    }

    fn ms_sort(nums: &Vec<i32>) -> (result: Vec<i32>) {
        let n = nums.len();
        if n <= 1 {
            let mut result: Vec<i32> = Vec::new();
            if n == 1 {
                result.push(nums[0]);
            }
            return result;
        }

        let mid = n / 2;

        let mut left: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < mid {
            left.push(nums[i]);
            i = i + 1;
        }

        let mut right: Vec<i32> = Vec::new();
        let mut j: usize = mid;
        while j < n {
            right.push(nums[j]);
            j = j + 1;
        }

        let sorted_left = Self::ms_sort(&left);
        let sorted_right = Self::ms_sort(&right);
        let result = Self::ms_merge(&sorted_left, &sorted_right);
        result
    }

    pub fn sort_array(nums: Vec<i32>) -> (res: Vec<i32>)
        requires
            1 <= nums.len() <= 50_000,
            forall|i: int| 0 <= i < nums.len() ==> -50_000 <= #[trigger] nums[i] <= 50_000,
        ensures
            Self::sorted(res@),
            Self::is_perm(res@, nums@),
    {
        Self::ms_sort(&nums)
    }
}

}
