use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_mountain(s: Seq<i32>, peak: int) -> bool {
        s.len() >= 3
        && 0 < peak < s.len() - 1
        && (forall |a: int, b: int| 0 <= a < b <= peak ==> s[a] < s[b])
        && (forall |a: int, b: int| peak <= a < b < s.len() ==> s[a] > s[b])
    }

    pub fn peak_index_in_mountain_array(arr: Vec<i32>) -> (result: i32)
        requires
            3 <= arr.len() <= 100_000,
            forall |i: int| 0 <= i < arr.len() ==> 0 <= #[trigger] arr[i] <= 1_000_000,
            exists |peak: int| Self::is_mountain(arr@, peak),
        ensures
            0 < result < arr.len() - 1,
            Self::is_mountain(arr@, result as int),
    {
        let n = arr.len();
        let mut left: usize = 0;
        let mut right: usize = n - 1;
        while left < right {
            let mid = left + (right - left) / 2;
            if arr[mid] < arr[mid + 1] {
                left = mid + 1;
            } else {
                right = mid;
            }
        }
        left as i32
    }
}

}
