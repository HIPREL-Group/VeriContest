use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub fn get_last_moment(n: i32, left: Vec<i32>, right: Vec<i32>) -> (res: i32)
        requires
            1 <= n <= 10_000,
            left.len() + right.len() >= 1,
            left.len() + right.len() <= n + 1,
            forall |i: int| 0 <= i < left.len() ==> 0 <= #[trigger] left[i] <= n,
            forall |i: int| 0 <= i < right.len() ==> 0 <= #[trigger] right[i] <= n,
        ensures
            0 <= res <= n,
            forall |i: int| 0 <= i < left.len() ==> res >= #[trigger] left[i],
            forall |i: int| 0 <= i < right.len() ==> res >= n - #[trigger] right[i],
            (exists |k: int| 0 <= k < left.len() && res == left[k])
            || (exists |k: int| 0 <= k < right.len() && res == n - right[k]),
    {
        let mut max_left: i32 = 0;
        let mut i: usize = 0;
        while i < left.len() {
            if left[i] >= max_left {
                max_left = left[i];
            }
            i = i + 1;
        }
        let mut min_right: i32 = n;
        let mut j: usize = 0;
        while j < right.len() {
            if right[j] <= min_right {
                min_right = right[j];
            }
            j = j + 1;
        }
        if max_left >= n - min_right {
            max_left
        } else {
            n - min_right
        }
    }
}

}
