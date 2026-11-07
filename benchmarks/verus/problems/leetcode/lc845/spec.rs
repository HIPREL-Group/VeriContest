use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_mountain_subarray(s: Seq<i32>, l: int, r: int, peak: int) -> bool {
        0 <= l && l < peak && peak < r && r < s.len()
        && (forall |a: int, b: int| l <= a < b <= peak ==> s[a] < s[b])
        && (forall |a: int, b: int| peak <= a < b <= r ==> s[a] > s[b])
    }

    pub fn longest_mountain(arr: Vec<i32>) -> (result: i32)
        requires
            1 <= arr.len() <= 10_000,
            forall |k: int| 0 <= k < arr.len() ==> 0 <= #[trigger] arr[k] <= 10_000,
        ensures
            result >= 0,
            result > 0 ==> (exists |l: int, r: int, peak: int|
                #[trigger] Self::is_mountain_subarray(arr@, l, r, peak)
                && r - l + 1 == result as int),
            result == 0 ==> (forall |l: int, r: int, peak: int|
                !Self::is_mountain_subarray(arr@, l, r, peak)),
            forall |l: int, r: int, peak: int|
                #[trigger] Self::is_mountain_subarray(arr@, l, r, peak)
                ==> r - l + 1 <= result as int,
    {
    }
}

}
