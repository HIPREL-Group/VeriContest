use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_sorted(s: Seq<i32>) -> bool {
        forall |i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
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

    pub open spec fn window_diff(s: Seq<i32>, k: int, j: int) -> int {
        s[j + k - 1] as int - s[j] as int
    }

    pub fn minimum_difference(nums: Vec<i32>, k: i32) -> (res: i32)
        requires
            1 <= k <= nums.len() <= 1000,
            forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 100_000,
        ensures
            0 <= res <= 100_000,
            exists |sorted_seq: Seq<i32>|
                Self::is_sorted(sorted_seq)
                && Self::is_perm(sorted_seq, nums@)
                && (forall |j: int| 0 <= j <= sorted_seq.len() - k as int ==>
                    #[trigger] Self::window_diff(sorted_seq, k as int, j) >= res as int)
                && (exists |j: int| 0 <= j <= sorted_seq.len() - k as int
                    && res as int == Self::window_diff(sorted_seq, k as int, j)),
    {
    }
}

}