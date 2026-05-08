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

    pub fn valid_mountain_array(arr: Vec<i32>) -> (result: bool)
        requires
            1 <= arr.len() <= 10_000,
            forall |k: int| 0 <= k < arr.len() ==> 0 <= #[trigger] arr[k] <= 10_000,
        ensures
            result == (exists |peak: int| Self::is_mountain(arr@, peak)),
    {
        let n = arr.len();
        if n < 3 {
            return false;
        }

        let mut i: usize = 0;

        while i + 1 < n && arr[i] < arr[i + 1] {
            i = i + 1;
        }

        if i == 0 {
            return false;
        }

        if i == n - 1 {
            return false;
        }

        let peak = i;

        while i + 1 < n && arr[i] > arr[i + 1] {
            i = i + 1;
        }

        if i == n - 1 {
            return true;
        } else {
            return false;
        }
    }
}

}
