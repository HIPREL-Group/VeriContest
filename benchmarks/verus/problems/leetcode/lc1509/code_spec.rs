use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn num_changes(a: Seq<i32>, b: Seq<i32>) -> int
        decreases a.len(),
    {
        if a.len() == 0 || a.len() != b.len() { 0 }
        else {
            (if a.last() != b.last() { 1int } else { 0int })
                + Self::num_changes(a.drop_last(), b.drop_last())
        }
    }

    pub open spec fn seq_max(s: Seq<i32>) -> int
        decreases s.len(),
    {
        if s.len() <= 0 { i32::MIN as int }
        else if s.len() == 1 { s[0] as int }
        else {
            let rest = Self::seq_max(s.drop_last());
            if s.last() as int >= rest { s.last() as int } else { rest }
        }
    }

    pub open spec fn seq_min(s: Seq<i32>) -> int
        decreases s.len(),
    {
        if s.len() <= 0 { i32::MAX as int }
        else if s.len() == 1 { s[0] as int }
        else {
            let rest = Self::seq_min(s.drop_last());
            if (s.last() as int) <= rest { s.last() as int } else { rest }
        }
    }

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

    pub open spec fn is_permutation(a: Seq<i32>, b: Seq<i32>) -> bool {
        forall |v: i32| Self::count_occ(a, v) == Self::count_occ(b, v)
    }

    fn ms_merge(a: &Vec<i32>, b: &Vec<i32>) -> (result: Vec<i32>)
        requires Self::is_sorted(a@), Self::is_sorted(b@)
        ensures
            Self::is_sorted(result@),
            result@.len() == a@.len() + b@.len(),
            Self::is_permutation(result@, a@ + b@),
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
            result@.len() == input@.len(),
            Self::is_permutation(result@, input@),
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

    pub fn min_difference(nums: Vec<i32>) -> (res: i32)
        requires
            1 <= nums.len() <= 100_000,
            forall |i: int| 0 <= i < nums.len() ==> -1_000_000_000 <= #[trigger] nums[i] <= 1_000_000_000,
        ensures
            nums.len() <= 4 ==> res == 0,
            nums.len() > 4 ==> (
                exists |m: Seq<i32>|
                    m.len() == nums.len()
                    && Self::num_changes(nums@, m) <= 3
                    && res as int == Self::seq_max(m) - Self::seq_min(m)
                    && forall |m2: Seq<i32>|
                        m2.len() == nums.len()
                        && Self::num_changes(nums@, m2) <= 3
                        ==> Self::seq_max(m2) - Self::seq_min(m2) >= res as int
            ),
    {
        let n = nums.len();
        if n <= 4 { return 0; }

        let nums = Self::ms_sort(&nums);

        let d1 = nums[n - 1] - nums[3];
        let d2 = nums[n - 2] - nums[2];
        let d3 = nums[n - 3] - nums[1];
        let d4 = nums[n - 4] - nums[0];
        let mut result = d1;
        if d2 < result {
            result = d2;
        }
        if d3 < result {
            result = d3;
        }
        if d4 < result {
            result = d4;
        }
        result
    }
}

}