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
        let ghost mut ml_idx: int = -1;
        let mut i: usize = 0;

        while i < left.len()
            invariant
                0 <= i <= left.len(),
                0 <= max_left <= n,
                1 <= n <= 10_000,
                forall |k: int| 0 <= k < left.len() ==> 0 <= #[trigger] left[k] <= n,
                forall |k: int| 0 <= k < i ==> max_left >= left[k],
                i == 0 ==> (max_left == 0 && ml_idx == -1),
                i > 0 ==> (0 <= ml_idx < i && max_left == left[ml_idx]),
            decreases left.len() - i,
        {
            if left[i] >= max_left {
                max_left = left[i];
                proof { ml_idx = i as int; }
            }
            i = i + 1;
        }

        let mut min_right: i32 = n;
        let ghost mut mr_idx: int = -1;
        let mut j: usize = 0;

        while j < right.len()
            invariant
                0 <= j <= right.len(),
                0 <= min_right <= n,
                1 <= n <= 10_000,
                forall |k: int| 0 <= k < right.len() ==> 0 <= #[trigger] right[k] <= n,
                forall |k: int| 0 <= k < j ==> min_right <= right[k],
                j == 0 ==> (min_right == n && mr_idx == -1),
                j > 0 ==> (0 <= mr_idx < j && min_right == right[mr_idx]),
            decreases right.len() - j,
        {
            if right[j] <= min_right {
                min_right = right[j];
                proof { mr_idx = j as int; }
            }
            j = j + 1;
        }

        if max_left >= n - min_right {
            proof {
                assert forall |k: int| 0 <= k < right.len() implies max_left >= n - #[trigger] right[k] by {
                    assert(min_right <= right[k]);
                }
                if left.len() > 0 {
                    assert(0 <= ml_idx < left.len() && max_left == left[ml_idx]);
                } else {
                    assert(right.len() > 0);
                    assert(max_left == 0);
                    assert(min_right == n);
                    assert(0 <= mr_idx < right.len());
                    assert(max_left == n - right[mr_idx]);
                }
            }
            max_left
        } else {
            proof {
                assert forall |k: int| 0 <= k < left.len() implies n - min_right >= #[trigger] left[k] by {
                    assert(max_left >= left[k]);
                }
                assert(right.len() > 0);
                assert(0 <= mr_idx < right.len());
                assert(n - min_right == n - right[mr_idx]);
            }
            n - min_right
        }
    }
}

}
