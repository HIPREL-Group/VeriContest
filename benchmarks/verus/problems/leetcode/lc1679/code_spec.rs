use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn all_indices_distinct(left_idx: Seq<int>, right_idx: Seq<int>) -> bool {
    &&& forall |i: int, j: int| 0 <= i < j < left_idx.len()
        ==> left_idx[i] != left_idx[j]
    &&& forall |i: int, j: int| 0 <= i < j < right_idx.len()
        ==> right_idx[i] != right_idx[j]
    &&& forall |i: int, j: int| 0 <= i < left_idx.len() && 0 <= j < right_idx.len()
        ==> left_idx[i] != right_idx[j]
}

pub open spec fn is_valid_matching(nums: Seq<i32>, left_idx: Seq<int>, right_idx: Seq<int>, k: int) -> bool {
    &&& left_idx.len() == right_idx.len()
    &&& forall |i: int| 0 <= i < left_idx.len() ==> {
        &&& 0 <= left_idx[i] < nums.len()
        &&& 0 <= right_idx[i] < nums.len()
        &&& left_idx[i] != right_idx[i]
        &&& nums[left_idx[i]] as int + nums[right_idx[i]] as int == k
    }
    &&& all_indices_distinct(left_idx, right_idx)
}

impl Solution {
    pub open spec fn is_sorted(s: Seq<i32>) -> bool {
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
        a.len() == b.len() && forall |v: i32| Self::count_occ(a, v) == Self::count_occ(b, v)
    }

    fn ms_merge(a: &Vec<i32>, b: &Vec<i32>) -> (result: Vec<i32>)
        requires Self::is_sorted(a@), Self::is_sorted(b@)
        ensures
            Self::is_sorted(result@),
            result@.len() == a@.len() + b@.len(),
            Self::is_perm(result@, a@ + b@),
    {
        let mut result: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        let mut j: usize = 0;
        while i < a.len() || j < b.len()
        {
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

    fn ms_sort(input: &Vec<i32>) -> (result: Vec<i32>)
        ensures
            Self::is_sorted(result@),
            Self::is_perm(result@, input@),
        decreases input.len(),
    {
        let n = input.len();
        if n <= 1 {
            let mut result = Vec::new();
            if n == 1 {
                result.push(input[0]);
            }
            return result;
        }
        let mid = n / 2;
        let mut left: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < mid
        {
            left.push(input[i]);
            i = i + 1;
        }
        let mut right: Vec<i32> = Vec::new();
        let mut j: usize = mid;
        while j < n
        {
            right.push(input[j]);
            j = j + 1;
        }
        let sorted_left = Self::ms_sort(&left);
        let sorted_right = Self::ms_sort(&right);
        let result = Self::ms_merge(&sorted_left, &sorted_right);
        result
    }

    pub fn max_operations(nums: Vec<i32>, k: i32) -> (result: i32)
        requires
            1 <= nums.len() <= 100_000,
            forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000_000,
            1 <= k <= 1_000_000_000,
        ensures
            0 <= result,
            2 * result as int <= nums.len() as int,
            exists |left_idx: Seq<int>, right_idx: Seq<int>|
                is_valid_matching(nums@, left_idx, right_idx, k as int)
                && left_idx.len() == result as int,
            forall |left_idx: Seq<int>, right_idx: Seq<int>|
                is_valid_matching(nums@, left_idx, right_idx, k as int)
                ==> left_idx.len() <= result as int,
    {
        let nums = Self::ms_sort(&nums);
        let n = nums.len();
        let mut left: i64 = 0;
        let mut right: i64 = n as i64 - 1;
        let mut count: i32 = 0;
        while left < right
        {
            let sum = nums[left as usize] + nums[right as usize];
            if sum == k {
                count += 1;
                left += 1;
                right -= 1;
            } else if sum < k {
                left += 1;
            } else {
                right -= 1;
            }
        }
        count
    }
}

}
