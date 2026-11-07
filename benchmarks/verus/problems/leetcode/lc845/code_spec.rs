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
        let n = arr.len();
        if n < 3 {
            return 0;
        }

        let mut best: i32 = 0;
        let mut up: usize = 0;
        let mut down: usize = 0;
        let mut i: usize = 1;

        while i < n {
            if arr[i] > arr[i - 1] {
                if down > 0 {
                    up = 0;
                    down = 0;
                }
                up = up + 1;
            } else if arr[i] < arr[i - 1] {
                if up > 0 {
                    down = down + 1;
                }
            } else {
                up = 0;
                down = 0;
            }

            if up > 0 && down > 0 {
                let len = (up + down + 1) as i32;
                if len > best {
                    best = len;
                }
            }

            i = i + 1;
        }

        best
    }
}

}
