use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_sorted_seq(s: Seq<i32>) -> bool {
        forall |i: int, j: int| 0 <= i <= j < s.len() ==> s[i] <= s[j]
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
        forall |v: i32| Self::count_occ(a, v) == Self::count_occ(b, v)
    }

    pub open spec fn is_ap(s: Seq<i32>) -> bool {
        s.len() <= 1 || forall |i: int| 0 <= i < s.len() - 1 ==>
            s[i + 1] as int - (#[trigger] s[i]) as int == s[1] as int - s[0] as int
    }

    pub open spec fn can_form_ap(s: Seq<i32>) -> bool {
        exists |sorted: Seq<i32>|
            sorted.len() == s.len() &&
            Self::is_sorted_seq(sorted) &&
            Self::is_perm(s, sorted) &&
            Self::is_ap(sorted)
    }

    fn ms_merge(a: &Vec<i32>, b: &Vec<i32>) -> (result: Vec<i32>)
        requires
            Self::is_sorted_seq(a@),
            Self::is_sorted_seq(b@),
        ensures
            Self::is_sorted_seq(result@),
            result@.len() == a@.len() + b@.len(),
            Self::is_perm(result@, a@ + b@),
    {
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

    fn ms_sort(nums: &Vec<i32>) -> (result: Vec<i32>)
        ensures
            Self::is_sorted_seq(result@),
            result@.len() == nums@.len(),
            Self::is_perm(result@, nums@),
        decreases nums.len(),
    {
        let n = nums.len();
        if n <= 1 {
            let mut result = Vec::new();
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

    pub fn can_make_arithmetic_progression(arr: Vec<i32>) -> (res: bool)
        requires
            2 <= arr.len() <= 1000,
            forall |i: int| 0 <= i < arr.len() ==>
                -1_000_000 <= #[trigger] arr[i] <= 1_000_000,
        ensures
            res == Self::can_form_ap(arr@),
    {
        let sorted = Self::ms_sort(&arr);
        let n = sorted.len();
        if n <= 1 {
            return true;
        }
        let d = sorted[1] - sorted[0];
        let mut i: usize = 2;
        while i < n {
            if sorted[i] - sorted[i - 1] != d {
                return false;
            }
            i = i + 1;
        }
        true
    }
}

}
