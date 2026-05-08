use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn min_i32(a: i32, b: i32) -> i32 {
    if a <= b { a } else { b }
}

pub open spec fn max_len(rectangles: Seq<Vec<i32>>, n: int) -> i32
    decreases n,
{
    if n <= 0 {
        0
    } else {
        let side = min_i32(rectangles[n - 1][0], rectangles[n - 1][1]);
        let prev = max_len(rectangles, n - 1);
        if side > prev { side } else { prev }
    }
}

pub open spec fn count_max(rectangles: Seq<Vec<i32>>, n: int, mx: i32) -> int
    decreases n,
{
    if n <= 0 {
        0
    } else {
        let side = min_i32(rectangles[n - 1][0], rectangles[n - 1][1]);
        count_max(rectangles, n - 1, mx) + if side == mx { 1int } else { 0int }
    }
}

proof fn max_len_greater_means_all_less(rectangles: Seq<Vec<i32>>, n: int, new_side: i32)
    requires
        0 <= n <= rectangles.len(),
        forall |i: int| 0 <= i < rectangles.len() ==>
            (#[trigger] rectangles[i]).len() == 2,
        new_side > max_len(rectangles, n),
    ensures
        forall |j: int| 0 <= j < n ==>
            min_i32(#[trigger] rectangles[j][0], rectangles[j][1]) < new_side,
    decreases n,
{
    if n > 0 {
        max_len_greater_means_all_less(rectangles, n - 1, new_side);
    }
}

proof fn count_max_zero_when_greater(rectangles: Seq<Vec<i32>>, n: int, mx: i32)
    requires
        0 <= n <= rectangles.len(),
        forall |i: int| 0 <= i < rectangles.len() ==>
            (#[trigger] rectangles[i]).len() == 2,
        forall |j: int| 0 <= j < n ==>
            min_i32(#[trigger] rectangles[j][0], rectangles[j][1]) < mx,
    ensures
        count_max(rectangles, n, mx) == 0,
    decreases n,
{
    if n > 0 {
        count_max_zero_when_greater(rectangles, n - 1, mx);
    }
}

proof fn count_max_upper_bound(rectangles: Seq<Vec<i32>>, n: int, mx: i32)
    requires
        0 <= n <= rectangles.len(),
        forall |i: int| 0 <= i < rectangles.len() ==>
            (#[trigger] rectangles[i]).len() == 2,
    ensures
        count_max(rectangles, n, mx) <= n,
    decreases n,
{
    if n > 0 {
        count_max_upper_bound(rectangles, n - 1, mx);
    }
}

impl Solution {
    pub fn count_good_rectangles(rectangles: Vec<Vec<i32>>) -> (res: i32)
        requires
            1 <= rectangles.len() <= 1000,
            forall |i: int| 0 <= i < rectangles.len() ==>
                (#[trigger] rectangles[i]).len() == 2,
            forall |i: int| 0 <= i < rectangles.len() ==>
                1 <= (#[trigger] rectangles[i])[0] <= 1_000_000_000,
            forall |i: int| 0 <= i < rectangles.len() ==>
                1 <= (#[trigger] rectangles[i])[1] <= 1_000_000_000,
        ensures
            res == count_max(rectangles@, rectangles@.len() as int, max_len(rectangles@, rectangles@.len() as int)),
    {
        let mut cnt: i32 = 0;
        let mut mx: i32 = 0;
        let n = rectangles.len();
        let mut i = 0;
        while i < n
            invariant
                0 <= i <= n,
                n == rectangles.len(),
                1 <= n <= 1000,
                forall |k: int| 0 <= k < n ==>
                    (#[trigger] rectangles@[k]).len() == 2,
                forall |k: int| 0 <= k < n ==>
                    1 <= (#[trigger] rectangles@[k])[0] <= 1_000_000_000,
                forall |k: int| 0 <= k < n ==>
                    1 <= (#[trigger] rectangles@[k])[1] <= 1_000_000_000,
                mx == max_len(rectangles@, i as int),
                cnt as int == count_max(rectangles@, i as int, mx),
                0 <= cnt <= i as i32,
                i == 0 ==> mx == 0,
                i > 0 ==> 1 <= mx <= 1_000_000_000,
            decreases n - i,
        {
            let l = rectangles[i][0];
            let w = rectangles[i][1];
            let side = if l <= w { l } else { w };

            if side > mx {
                proof {
                    max_len_greater_means_all_less(rectangles@, i as int, side);
                    count_max_zero_when_greater(rectangles@, i as int, side);
                }
                cnt = 1;
                mx = side;
            } else if side == mx {
                proof {
                    count_max_upper_bound(rectangles@, i as int, mx);
                }
                cnt += 1;
            }
            i += 1;
        }
        cnt
    }
}

}
