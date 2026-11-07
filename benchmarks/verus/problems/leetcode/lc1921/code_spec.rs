use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn is_sorted(s: Seq<i32>) -> bool {
    forall |i: int, j: int| 0 <= i <= j < s.len() ==> s[i] <= s[j]
}

pub open spec fn count_occurrences(s: Seq<i32>, val: i32) -> int
    decreases s.len(),
{
    if s.len() == 0 { 0 }
    else {
        (if s.last() == val { 1int } else { 0int })
            + count_occurrences(s.drop_last(), val)
    }
}

pub open spec fn is_permutation(a: Seq<i32>, b: Seq<i32>) -> bool {
    forall |v: i32| count_occurrences(a, v) == count_occurrences(b, v)
}

pub open spec fn count_leq(s: Seq<i32>, threshold: int, end: int) -> int
    decreases end
{
    if end <= 0 { 0 }
    else {
        count_leq(s, threshold, end - 1)
            + if s[end - 1] as int <= threshold { 1int } else { 0int }
    }
}

pub struct Solution;

impl Solution {
    pub open spec fn arrival_time(d: int, s: int) -> int {
        (d + s - 1) / s
    }

    pub open spec fn count_le(dist: Seq<i32>, speed: Seq<i32>, t: int, end: int) -> int
        decreases end
    {
        if end <= 0 {
            0
        } else {
            Self::count_le(dist, speed, t, end - 1)
                + if Self::arrival_time(dist[end - 1] as int, speed[end - 1] as int) <= t {
                    1int
                } else {
                    0int
                }
        }
    }

    fn merge(a: &Vec<i32>, b: &Vec<i32>) -> (result: Vec<i32>)
        requires
            is_sorted(a@),
            is_sorted(b@),
        ensures
            is_sorted(result@),
            result@.len() == a@.len() + b@.len(),
            is_permutation(result@, a@ + b@),
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

    fn merge_sort(nums: &Vec<i32>) -> (result: Vec<i32>)
        ensures
            is_sorted(result@),
            result@.len() == nums@.len(),
            is_permutation(result@, nums@),
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
        while i < mid
        {
            left.push(nums[i]);
            i = i + 1;
        }
        let mut right: Vec<i32> = Vec::new();
        let mut j: usize = mid;
        while j < n
        {
            right.push(nums[j]);
            j = j + 1;
        }
        let sorted_left = Self::merge_sort(&left);
        let sorted_right = Self::merge_sort(&right);
        let result = Self::merge(&sorted_left, &sorted_right);
        result
    }

    pub fn eliminate_maximum(dist: Vec<i32>, speed: Vec<i32>) -> (result: i32)
        requires
            dist.len() == speed.len(),
            1 <= dist.len() <= 100_000,
            forall |i: int| 0 <= i < dist.len() ==> 1 <= #[trigger] dist[i] <= 100_000,
            forall |i: int| 0 <= i < speed.len() ==> 1 <= #[trigger] speed[i] <= 100_000,
        ensures
            0 <= result <= dist.len(),
            forall |t: int| 0 <= t < result ==>
                Self::count_le(dist@, speed@, t, dist.len() as int) <= t,
            result < dist.len() as int ==>
                Self::count_le(dist@, speed@, result as int, dist.len() as int) > result as int,
    {
        let n = dist.len();
        let mut arrivals: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n
        {
            let arrival = (dist[i] + speed[i] - 1) / speed[i];
            arrivals.push(arrival);
            i = i + 1;
        }
        let sorted = Self::merge_sort(&arrivals);
        let mut t: usize = 0;
        while t < n
        {
            if sorted[t] <= t as i32 {
                return t as i32;
            }
            t = t + 1;
        }
        n as i32
    }
}

}
