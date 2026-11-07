use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_i2min(a: int, b: int) -> int {
    if a < b {
        a
    } else {
        b
    }
}

pub open spec fn spec_i2max(a: int, b: int) -> int {
    if a > b {
        a
    } else {
        b
    }
}

pub open spec fn spec_min_first_i(s: Seq<i64>, i: int) -> int
    recommends
        s.len() == 4,
        1 <= i <= 4,
{
    if i == 1 {
        s[0] as int
    } else if i == 2 {
        spec_i2min(s[0] as int, s[1] as int)
    } else if i == 3 {
        spec_i2min(spec_i2min(s[0] as int, s[1] as int), s[2] as int)
    } else {
        spec_i2min(
            spec_i2min(s[0] as int, s[1] as int),
            spec_i2min(s[2] as int, s[3] as int),
        )
    }
}

pub open spec fn spec_max_first_i(s: Seq<i64>, i: int) -> int
    recommends
        s.len() == 4,
        1 <= i <= 4,
{
    if i == 1 {
        s[0] as int
    } else if i == 2 {
        spec_i2max(s[0] as int, s[1] as int)
    } else if i == 3 {
        spec_i2max(spec_i2max(s[0] as int, s[1] as int), s[2] as int)
    } else {
        spec_i2max(
            spec_i2max(s[0] as int, s[1] as int),
            spec_i2max(s[2] as int, s[3] as int),
        )
    }
}

pub open spec fn spec_axis_span(s: Seq<i64>) -> int
    recommends
        s.len() == 4,
{
    spec_max_first_i(s, 4) - spec_min_first_i(s, 4)
}

pub open spec fn is_corner_of_square(x: int, y: int, x_lo: int, x_hi: int, y_lo: int, y_hi: int) -> bool {
    (x == x_lo || x == x_hi) && (y == y_lo || y == y_hi)
}

pub open spec fn point_matches(xs: Seq<i64>, ys: Seq<i64>, i: int, x: int, y: int) -> bool {
    xs[i] as int == x && ys[i] as int == y
}

pub open spec fn square_corners_span(x_lo: int, x_hi: int, y_lo: int, y_hi: int) -> bool {
    x_lo < x_hi && y_lo < y_hi && (x_hi - x_lo) == (y_hi - y_lo)
}

pub open spec fn is_axis_aligned_square(xs: Seq<i64>, ys: Seq<i64>) -> bool
    recommends
        xs.len() == 4,
        ys.len() == 4,
{
    exists|x_lo: int, x_hi: int, y_lo: int, y_hi: int|
        #[trigger] square_corners_span(x_lo, x_hi, y_lo, y_hi)
        && (forall|i: int| 0 <= i < 4 ==> #[trigger] is_corner_of_square(xs[i] as int, ys[i] as int, x_lo, x_hi, y_lo, y_hi))
        && (exists|i: int| 0 <= i < 4 && #[trigger] point_matches(xs, ys, i, x_lo, y_lo))
        && (exists|i: int| 0 <= i < 4 && #[trigger] point_matches(xs, ys, i, x_lo, y_hi))
        && (exists|i: int| 0 <= i < 4 && #[trigger] point_matches(xs, ys, i, x_hi, y_lo))
        && (exists|i: int| 0 <= i < 4 && #[trigger] point_matches(xs, ys, i, x_hi, y_hi))
}

impl Solution {
    pub fn axis_aligned_square_area(xs: Vec<i64>, ys: Vec<i64>) -> (res: i64)
        requires
            xs.len() == 4,
            ys.len() == 4,
            forall|j: int|
                0 <= j < 4 ==> -1000 <= (#[trigger] xs[j] as int) && (xs[j] as int) <= 1000 && -1000 <= (ys[j] as int) && (ys[j] as int) <= 1000,
            is_axis_aligned_square(xs@, ys@),
        ensures
            res as int == spec_axis_span(xs@) * spec_axis_span(ys@),
    {
        let mut min_x = xs[0];
        let mut max_x = xs[0];
        let mut i = 1usize;
        while i < 4 {
            if xs[i] < min_x {
                min_x = xs[i];
            }
            if xs[i] > max_x {
                max_x = xs[i];
            }
            i = i + 1;
        }
        let mut min_y = ys[0];
        let mut max_y = ys[0];
        let mut j = 1usize;
        while j < 4 {
            if ys[j] < min_y {
                min_y = ys[j];
            }
            if ys[j] > max_y {
                max_y = ys[j];
            }
            j = j + 1;
        }
        let sx = max_x - min_x;
        let sy = max_y - min_y;
        sx * sy
    }
}

}
