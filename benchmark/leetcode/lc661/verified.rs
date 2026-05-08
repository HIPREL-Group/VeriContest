use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

proof fn div_i32_matches_int(sum: i32, count: i32)
    requires
        0 <= sum,
        1 <= count,
    ensures
        (sum / count) as int == (sum as int) / (count as int),
{
}

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
        let rows = img.len();
        let cols = img[0].len();
        let mut result: Vec<Vec<i32>> = Vec::new();
        let mut i: usize = 0;
        while i < rows
            invariant
                rows == img.len(),
                cols == img[0].len(),
                1 <= rows <= 200,
                1 <= cols <= 200,
                forall |r: int| 0 <= r < rows ==> #[trigger] img[r].len() == cols,
                forall |r: int, c: int| 0 <= r < rows && 0 <= c < img[r].len() ==> 0 <= #[trigger] img[r][c] <= 255,
                i <= rows,
                result.len() == i,
                forall |r: int| 0 <= r < i ==> #[trigger] result[r].len() == cols,
                forall |r: int, c: int| 0 <= r < i && 0 <= c < result[r].len() ==> #[trigger] result[r][c] as int == Self::smooth_value(img@, r, c),
            decreases rows - i,
        {
            let mut row: Vec<i32> = Vec::new();
            let mut j: usize = 0;
            while j < cols
                invariant
                    rows == img.len(),
                    cols == img[0].len(),
                    1 <= rows <= 200,
                    1 <= cols <= 200,
                    forall |r: int| 0 <= r < rows ==> #[trigger] img[r].len() == cols,
                    forall |r: int, c: int| 0 <= r < rows && 0 <= c < img[r].len() ==> 0 <= #[trigger] img[r][c] <= 255,
                    i < rows,
                    j <= cols,
                    row.len() == j,
                    forall |c: int| 0 <= c < row.len() ==> #[trigger] row[c] as int == Self::smooth_value(img@, i as int, c),
                decreases cols - j,
            {
                let top = if i > 0 { i - 1 } else { 0 };
                let bottom = if i + 2 <= rows { i + 2 } else { rows };
                let left = if j > 0 { j - 1 } else { 0 };
                let right = if j + 2 <= cols { j + 2 } else { cols };

                proof {
                    assert(top as int == Self::window_start(i as int));
                    assert(bottom as int == Self::window_end(i as int, rows as int));
                    assert(left as int == Self::window_start(j as int));
                    assert(right as int == Self::window_end(j as int, cols as int));
                    assert(top <= i < bottom);
                    assert(left <= j < right);
                    assert(0 < bottom as int - top as int <= 3);
                    assert(0 < right as int - left as int <= 3);
                }

                let mut sum: i32 = 0;
                let mut count: i32 = 0;
                let mut x: usize = top;
                while x < bottom
                    invariant
                        rows == img.len(),
                        cols == img[0].len(),
                        1 <= rows <= 200,
                        1 <= cols <= 200,
                        forall |r: int| 0 <= r < rows ==> #[trigger] img[r].len() == cols,
                        forall |r: int, c: int| 0 <= r < rows && 0 <= c < img[r].len() ==> 0 <= #[trigger] img[r][c] <= 255,
                        i < rows,
                        j < cols,
                        top <= x <= bottom <= rows,
                        left <= right <= cols,
                        top <= i < bottom,
                        left <= j < right,
                        0 < bottom as int - top as int <= 3,
                        0 < right as int - left as int <= 3,
                        sum as int == Self::rect_sum(img@, top as int, x as int, left as int, right as int),
                        count as int == (x as int - top as int) * (right as int - left as int),
                        0 <= count as int <= 9,
                        0 <= sum as int <= 255 * count as int,
                    decreases bottom - x,
                {
                    let mut y: usize = left;
                    while y < right
                        invariant
                            rows == img.len(),
                            cols == img[0].len(),
                            1 <= rows <= 200,
                            1 <= cols <= 200,
                            forall |r: int| 0 <= r < rows ==> #[trigger] img[r].len() == cols,
                            forall |r: int, c: int| 0 <= r < rows && 0 <= c < img[r].len() ==> 0 <= #[trigger] img[r][c] <= 255,
                            top <= x < bottom <= rows,
                            left <= y <= right <= cols,
                            0 < bottom as int - top as int <= 3,
                            0 < right as int - left as int <= 3,
                            sum as int == Self::rect_sum(img@, top as int, x as int, left as int, right as int)
                                + Self::row_sum(img@, x as int, left as int, y as int),
                            count as int == (x as int - top as int) * (right as int - left as int) + (y as int - left as int),
                            0 <= count as int <= 9,
                            0 <= sum as int <= 255 * count as int,
                        decreases right - y,
                    {
                        let prev_sum = sum;
                        let prev_count = count;
                        proof {
                            assert(img[x as int].len() == cols);
                            assert(y < cols);
                            assert(y < img[x as int].len());
                        }
                        let v = img[x][y];
                        proof {
                            assert(0 <= v <= 255);
                            assert(prev_sum as int + v as int <= 255 * prev_count as int + 255) by (nonlinear_arith)
                                requires
                                    0 <= prev_sum as int <= 255 * prev_count as int,
                                    0 <= v as int <= 255;
                            assert(prev_sum as int + v as int <= 255 * 9 + 255) by (nonlinear_arith)
                                requires
                                    prev_sum as int + v as int <= 255 * prev_count as int + 255,
                                    prev_count as int <= 9;
                            assert(255 * 9 < i32::MAX);
                            assert(255 * 9 + 255 < i32::MAX);
                            assert(prev_sum as int + v as int <= i32::MAX) by (nonlinear_arith)
                                requires
                                    prev_sum as int + v as int <= 255 * 9 + 255,
                                    255 * 9 + 255 < i32::MAX;
                        }
                        sum = sum + v;
                        count = count + 1;
                        proof {
                            assert(Self::row_sum(img@, x as int, left as int, y as int + 1)
                                == Self::row_sum(img@, x as int, left as int, y as int) + img[x as int][y as int] as int);
                            assert(sum as int == prev_sum as int + v as int);
                            assert(count as int == prev_count as int + 1);
                            assert(0 <= count as int);
                            assert(x as int - top as int <= 2) by (nonlinear_arith)
                                requires
                                    x < bottom,
                                    0 < bottom as int - top as int <= 3;
                            assert(y as int - left as int <= 2) by (nonlinear_arith)
                                requires
                                    y < right,
                                    0 < right as int - left as int <= 3;
                            assert(count as int <= 9) by (nonlinear_arith)
                                requires
                                    count as int == prev_count as int + 1,
                                    prev_count as int == (x as int - top as int) * (right as int - left as int) + (y as int - left as int),
                                    x as int - top as int <= 2,
                                    y as int - left as int <= 2,
                                    0 < right as int - left as int <= 3;
                            assert(0 <= sum as int);
                            assert(sum as int <= 255 * count as int) by (nonlinear_arith)
                                requires
                                    0 <= prev_sum as int,
                                    prev_sum as int <= 255 * prev_count as int,
                                    0 <= v as int <= 255,
                                    count as int == prev_count as int + 1,
                                    sum as int == prev_sum as int + v as int;
                        }
                        y += 1;
                    }
                    proof {
                        assert(Self::rect_sum(img@, top as int, x as int + 1, left as int, right as int)
                            == Self::rect_sum(img@, top as int, x as int, left as int, right as int)
                                + Self::row_sum(img@, x as int, left as int, right as int));
                        assert(count as int == ((x as int + 1) - top as int) * (right as int - left as int)) by (nonlinear_arith)
                            requires
                                count as int == (x as int - top as int) * (right as int - left as int) + (right as int - left as int);
                    }
                    x += 1;
                }

                proof {
                    assert(count as int == (bottom as int - top as int) * (right as int - left as int));
                    assert(0 < (bottom as int - top as int) * (right as int - left as int)) by (nonlinear_arith)
                        requires
                            (top as int) <= (i as int),
                            (i as int) < (bottom as int),
                            (left as int) <= (j as int),
                            (j as int) < (right as int);
                    assert(0 < count as int);
                    assert(0 < count);
                    assert(0 <= sum);
                }
                let avg = sum / count;
                proof {
                    div_i32_matches_int(sum, count);
                    assert((avg as int) == (sum / count) as int);
                    assert((sum / count) as int
                        == Self::rect_sum(img@, top as int, bottom as int, left as int, right as int)
                            / ((bottom as int - top as int) * (right as int - left as int)));
                    assert(avg as int == Self::smooth_value(img@, i as int, j as int));
                }

                let ghost old_row = row@;
                row.push(avg);
                proof {
                    assert forall |c: int| 0 <= c < j as int + 1
                        implies #[trigger] row[c] as int == Self::smooth_value(img@, i as int, c)
                    by {
                        if c < j as int {
                            assert(row@[c] == old_row[c]);
                        } else {
                            assert(c == j as int);
                            assert(row@[c] == avg);
                        }
                    };
                }
                j += 1;
            }

            let ghost old_result = result@;
            let ghost row_snap = row@;
            result.push(row);
            proof {
                assert forall |r: int| 0 <= r < i as int + 1
                    implies #[trigger] result[r].len() == cols
                by {
                    if r < i as int {
                        assert(result@[r] == old_result[r]);
                    } else {
                        assert(r == i as int);
                        assert(result@[r]@ == row_snap);
                    }
                };
                assert forall |r: int, c: int| 0 <= r < i as int + 1 && 0 <= c < result[r].len()
                    implies #[trigger] result[r][c] as int == Self::smooth_value(img@, r, c)
                by {
                    if r < i as int {
                        assert(result@[r] == old_result[r]);
                    } else {
                        assert(r == i as int);
                        assert(result@[r]@ == row_snap);
                    }
                };
            }
            i += 1;
        }
        result
    }
}

}
