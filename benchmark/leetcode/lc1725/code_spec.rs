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
        {
            let l = rectangles[i][0];
            let w = rectangles[i][1];
            let side = if l <= w { l } else { w };
            if side > mx {
                cnt = 1;
                mx = side;
            } else if side == mx {
                cnt += 1;
            }
            i += 1;
        }
        cnt
    }
}

}
