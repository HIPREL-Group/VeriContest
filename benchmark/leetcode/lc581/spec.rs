use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn sorted(s: Seq<i32>) -> bool {
        forall |i: int, j: int|
            0 <= i < j < s.len() ==> s[i] <= s[j]
    }

    pub open spec fn sorted_range(s: Seq<i32>, lo: int, hi: int) -> bool {
        forall |i: int, j: int|
            lo <= i < j < hi ==> s[i] <= s[j]
    }

    pub open spec fn segment_min(s: Seq<i32>, start: int, end: int) -> int
        decreases end - start,
    {
        if start >= end {
            0
        } else if start + 1 >= end {
            s[start] as int
        } else {
            let rest = Self::segment_min(s, start + 1, end);
            let cur = s[start] as int;
            if cur <= rest { cur } else { rest }
        }
    }

    pub open spec fn segment_max(s: Seq<i32>, start: int, end: int) -> int
        decreases end - start,
    {
        if start >= end {
            0
        } else if start + 1 >= end {
            s[start] as int
        } else {
            let rest = Self::segment_max(s, start + 1, end);
            let cur = s[start] as int;
            if cur >= rest { cur } else { rest }
        }
    }

    pub open spec fn valid(s: Seq<i32>, left: int, right: int) -> bool {
        let n = s.len();
        0 <= left <= right < n
        && Self::sorted_range(s, 0, left)
        && Self::sorted_range(s, right + 1, n as int)
        && (forall |i: int| 0 <= i < left ==> s[i] <= Self::segment_min(s, left, right + 1))
        && (forall |j: int| right < j < n ==> s[j] >= Self::segment_max(s, left, right + 1))
    }

    pub fn find_unsorted_subarray(nums: Vec<i32>) -> (res: i32)
        requires
            1 <= nums.len() <= 10_000,
            forall |i: int| 0 <= i < nums.len() ==>
                -100_000 <= #[trigger] nums[i] <= 100_000,
        ensures
            res >= 0,
            res == 0 <==> Self::sorted(nums@),
            res > 0 ==> exists |left: int, right: int|
                0 <= left <= right < nums.len()
                && Self::valid(nums@, left, right)
                && res == (right - left + 1) as i32
                && (forall |l2: int, r2: int|
                    Self::valid(nums@, l2, r2) ==>
                    (right - left + 1) <= (r2 - l2 + 1)),
    {
    }
}

}