use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn window_start(idx: int) -> int {
        if idx > 0 { idx - 1 } else { 0 }
    }

    pub open spec fn window_end(idx: int, limit: int) -> int {
        if idx + 2 <= limit { idx + 2 } else { limit }
    }

    pub open spec fn row_sum(img: Seq<Vec<i32>>, row: int, start: int, end: int) -> int
        decreases end - start
    {
        if start >= end {
            0
        } else {
            Self::row_sum(img, row, start, end - 1) + img[row][end - 1] as int
        }
    }

    pub open spec fn rect_sum(img: Seq<Vec<i32>>, top: int, bottom: int, left: int, right: int) -> int
        decreases bottom - top
    {
        if top >= bottom {
            0
        } else {
            Self::rect_sum(img, top, bottom - 1, left, right)
                + Self::row_sum(img, bottom - 1, left, right)
        }
    }

    pub open spec fn smooth_value(img: Seq<Vec<i32>>, i: int, j: int) -> int {
        let top = Self::window_start(i);
        let bottom = Self::window_end(i, img.len() as int);
        let left = Self::window_start(j);
        let right = Self::window_end(j, img[i].len() as int);
        Self::rect_sum(img, top, bottom, left, right) / ((bottom - top) * (right - left))
    }

    pub fn image_smoother(img: Vec<Vec<i32>>) -> (res: Vec<Vec<i32>>)
        requires
            1 <= img.len() <= 200,
            1 <= img[0].len() <= 200,
            forall |i: int| 0 <= i < img.len() ==> #[trigger] img[i].len() == img[0].len(),
            forall |i: int, j: int| 0 <= i < img.len() && 0 <= j < img[i].len() ==> 0 <= #[trigger] img[i][j] <= 255,
        ensures
            res.len() == img.len(),
            forall |i: int| 0 <= i < res.len() ==> #[trigger] res[i].len() == img[i].len(),
            forall |i: int, j: int| 0 <= i < res.len() && 0 <= j < res[i].len() ==> #[trigger] res[i][j] as int == Self::smooth_value(img@, i, j),
    {
    }
}

}
