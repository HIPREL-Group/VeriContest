use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn row_segment(matrix: Seq<Vec<i32>>, row: int, left: int, right: int) -> Seq<i32>
        recommends
            0 <= row < matrix.len(),
            0 <= left <= right <= matrix[row].len(),
    {
        Seq::new((right - left) as nat, |i: int| matrix[row][left + i])
    }

    pub open spec fn col_segment(matrix: Seq<Vec<i32>>, col: int, top: int, bottom: int) -> Seq<i32>
        recommends
            0 <= top <= bottom <= matrix.len(),
            forall |r: int| 0 <= r < matrix.len() ==> col < #[trigger] matrix[r].len(),
    {
        Seq::new((bottom - top) as nat, |i: int| matrix[top + i][col])
    }

    pub open spec fn rev_row_segment(matrix: Seq<Vec<i32>>, row: int, left: int, right: int) -> Seq<i32>
        recommends
            0 <= row < matrix.len(),
            0 <= left <= right <= matrix[row].len(),
    {
        Seq::new((right - left) as nat, |i: int| matrix[row][right - 1 - i])
    }

    pub open spec fn rev_col_segment(matrix: Seq<Vec<i32>>, col: int, top: int, bottom: int) -> Seq<i32>
        recommends
            0 <= top <= bottom <= matrix.len(),
            forall |r: int| 0 <= r < matrix.len() ==> col < #[trigger] matrix[r].len(),
    {
        Seq::new((bottom - top) as nat, |i: int| matrix[bottom - 1 - i][col])
    }

    pub open spec fn layer_seq(matrix: Seq<Vec<i32>>, top: int, bottom: int, left: int, right: int) -> Seq<i32>
        recommends
            0 <= top < bottom <= matrix.len(),
            0 <= left < right,
            forall |r: int| 0 <= r < matrix.len() ==> right <= #[trigger] matrix[r].len(),
    {
        Self::row_segment(matrix, top, left, right)
        + Self::col_segment(matrix, right - 1, top + 1, bottom)
        + if top + 1 < bottom {
            Self::rev_row_segment(matrix, bottom - 1, left, right - 1)
        } else {
            seq![]
        }
        + if top + 1 < bottom && left + 1 < right {
            Self::rev_col_segment(matrix, left, top + 1, bottom - 1)
        } else {
            seq![]
        }
    }

    pub open spec fn spiral_region(matrix: Seq<Vec<i32>>, top: int, bottom: int, left: int, right: int) -> Seq<i32>
        recommends
            0 <= top <= bottom <= matrix.len(),
            0 <= left <= right,
            forall |r: int| 0 <= r < matrix.len() ==> right <= #[trigger] matrix[r].len(),
        decreases
            if top >= bottom || left >= right {
                0nat
            } else {
                (bottom - top + right - left) as nat
            },
    {
        if top >= bottom || left >= right {
            seq![]
        } else {
            Self::layer_seq(matrix, top, bottom, left, right)
            + if top + 1 < bottom && left + 1 < right {
                Self::spiral_region(matrix, top + 1, bottom - 1, left + 1, right - 1)
            } else {
                seq![]
            }
        }
    }

    proof fn lemma_row_segment_extend(matrix: Seq<Vec<i32>>, row: int, left: int, right: int)
        requires
            0 <= row < matrix.len(),
            0 <= left <= right < matrix[row].len(),
        ensures
            Self::row_segment(matrix, row, left, right + 1) =~= Self::row_segment(matrix, row, left, right).push(matrix[row][right]),
    {
        assert(Self::row_segment(matrix, row, left, right + 1).len() == Self::row_segment(matrix, row, left, right).push(matrix[row][right]).len());
        assert forall |k: int|
            0 <= k < Self::row_segment(matrix, row, left, right + 1).len()
            implies Self::row_segment(matrix, row, left, right + 1)[k] == Self::row_segment(matrix, row, left, right).push(matrix[row][right])[k]
        by {
            if k < right - left {
            } else {
                assert(k == right - left);
            }
        }
    }

    proof fn lemma_col_segment_extend(matrix: Seq<Vec<i32>>, col: int, top: int, bottom: int)
        requires
            0 <= top <= bottom < matrix.len(),
            forall |r: int| 0 <= r < matrix.len() ==> col < #[trigger] matrix[r].len(),
        ensures
            Self::col_segment(matrix, col, top, bottom + 1) =~= Self::col_segment(matrix, col, top, bottom).push(matrix[bottom][col]),
    {
        assert(Self::col_segment(matrix, col, top, bottom + 1).len() == Self::col_segment(matrix, col, top, bottom).push(matrix[bottom][col]).len());
        assert forall |k: int|
            0 <= k < Self::col_segment(matrix, col, top, bottom + 1).len()
            implies Self::col_segment(matrix, col, top, bottom + 1)[k] == Self::col_segment(matrix, col, top, bottom).push(matrix[bottom][col])[k]
        by {
            if k < bottom - top {
            } else {
                assert(k == bottom - top);
            }
        }
    }

    proof fn lemma_rev_row_segment_extend(matrix: Seq<Vec<i32>>, row: int, left: int, right: int)
        requires
            0 <= row < matrix.len(),
            0 <= left < right <= matrix[row].len(),
        ensures
            Self::rev_row_segment(matrix, row, left, right) =~= Self::rev_row_segment(matrix, row, left + 1, right).push(matrix[row][left]),
    {
        assert(Self::rev_row_segment(matrix, row, left, right).len() == Self::rev_row_segment(matrix, row, left + 1, right).push(matrix[row][left]).len());
        assert forall |k: int|
            0 <= k < Self::rev_row_segment(matrix, row, left, right).len()
            implies Self::rev_row_segment(matrix, row, left, right)[k] == Self::rev_row_segment(matrix, row, left + 1, right).push(matrix[row][left])[k]
        by {
            if k < right - left - 1 {
            } else {
                assert(k == right - left - 1);
            }
        }
    }

    proof fn lemma_rev_col_segment_extend(matrix: Seq<Vec<i32>>, col: int, top: int, bottom: int)
        requires
            0 <= top < bottom <= matrix.len(),
            forall |r: int| 0 <= r < matrix.len() ==> col < #[trigger] matrix[r].len(),
        ensures
            Self::rev_col_segment(matrix, col, top, bottom) =~= Self::rev_col_segment(matrix, col, top + 1, bottom).push(matrix[top][col]),
    {
        assert(Self::rev_col_segment(matrix, col, top, bottom).len() == Self::rev_col_segment(matrix, col, top + 1, bottom).push(matrix[top][col]).len());
        assert forall |k: int|
            0 <= k < Self::rev_col_segment(matrix, col, top, bottom).len()
            implies Self::rev_col_segment(matrix, col, top, bottom)[k] == Self::rev_col_segment(matrix, col, top + 1, bottom).push(matrix[top][col])[k]
        by {
            if k < bottom - top - 1 {
            } else {
                assert(k == bottom - top - 1);
            }
        }
    }

    pub fn spiral_order(matrix: Vec<Vec<i32>>) -> (res: Vec<i32>)
        requires
            1 <= matrix.len() <= 10,
            1 <= matrix[0].len() <= 10,
            forall |r: int| 0 <= r < matrix.len() ==> #[trigger] matrix[r].len() == matrix[0].len(),
            forall |r: int, c: int| 0 <= r < matrix.len() && 0 <= c < matrix[r].len() ==> -100 <= #[trigger] matrix[r][c] <= 100,
        ensures
            res@ == Self::spiral_region(matrix@, 0, matrix.len() as int, 0, matrix[0].len() as int),
    {
        let rows = matrix.len();
        let cols = matrix[0].len();
        let ghost full = Self::spiral_region(matrix@, 0, rows as int, 0, cols as int);

        let mut result: Vec<i32> = Vec::new();
        let mut top: usize = 0;
        let mut bottom: usize = rows;
        let mut left: usize = 0;
        let mut right: usize = cols;

        while top < bottom && left < right
            invariant
                rows == matrix.len(),
                cols == matrix[0].len(),
                1 <= rows <= 10,
                1 <= cols <= 10,
                0 <= top <= bottom <= rows,
                0 <= left <= right <= cols,
                forall |r: int| 0 <= r < rows ==> #[trigger] matrix[r].len() == cols,
                forall |r: int, c: int| 0 <= r < rows && 0 <= c < cols ==> -100 <= #[trigger] matrix[r][c] <= 100,
                result@ + Self::spiral_region(matrix@, top as int, bottom as int, left as int, right as int) == full,
            decreases (bottom as int - top as int) + (right as int - left as int),
        {
            let ghost base = result@;
            let layer_top = top;
            let layer_bottom = bottom;
            let layer_left = left;
            let layer_right = right;

            let mut c: usize = left;
            while c < right
                invariant
                    rows == matrix.len(),
                    cols == matrix[0].len(),
                    1 <= rows <= 10,
                    1 <= cols <= 10,
                    0 <= left <= c <= right <= cols,
                    0 <= top < bottom <= rows,
                    top == layer_top,
                    bottom == layer_bottom,
                    left == layer_left,
                    right == layer_right,
                    forall |r: int| 0 <= r < rows ==> #[trigger] matrix[r].len() == cols,
                    result@ == base + Self::row_segment(matrix@, layer_top as int, layer_left as int, c as int),
                decreases right - c,
            {
                proof {
                    assert(top < rows);
                    assert(c < cols);
                    assert(matrix[top as int].len() == cols);
                }
                let ghost prev = result@;
                let v = matrix[top][c];
                result.push(v);
                proof {
                    assert(prev == base + Self::row_segment(matrix@, layer_top as int, layer_left as int, c as int));
                    assert(result@ == prev.push(v));
                    Self::lemma_row_segment_extend(matrix@, layer_top as int, layer_left as int, c as int);
                }
                c += 1;
            }
            top += 1;

            proof {
                assert(result@ == base + Self::row_segment(matrix@, layer_top as int, layer_left as int, layer_right as int));
            }

            let ghost after_top = result@;
            let mut r: usize = top;
            while r < bottom
                invariant
                    rows == matrix.len(),
                    cols == matrix[0].len(),
                    1 <= rows <= 10,
                    1 <= cols <= 10,
                    top == layer_top + 1,
                    bottom == layer_bottom,
                    left == layer_left,
                    right == layer_right,
                    0 <= top <= r <= bottom <= rows,
                    0 <= left < right <= cols,
                    forall |rr: int| 0 <= rr < rows ==> #[trigger] matrix[rr].len() == cols,
                    result@ == after_top + Self::col_segment(matrix@, layer_right as int - 1, layer_top as int + 1, r as int),
                decreases bottom - r,
            {
                proof {
                    assert(r < rows);
                    assert(right > 0);
                    assert(right - 1 < cols);
                    assert(matrix[r as int].len() == cols);
                }
                let ghost prev = result@;
                let v = matrix[r][right - 1];
                result.push(v);
                proof {
                    assert(prev == after_top + Self::col_segment(matrix@, layer_right as int - 1, layer_top as int + 1, r as int));
                    assert(result@ == prev.push(v));
                    Self::lemma_col_segment_extend(matrix@, layer_right as int - 1, layer_top as int + 1, r as int);
                }
                r += 1;
            }
            right -= 1;

            proof {
                assert(result@ == after_top + Self::col_segment(matrix@, layer_right as int - 1, layer_top as int + 1, layer_bottom as int));
            }

            let ghost after_right = result@;
            if top < bottom {
                let mut c2: usize = right;
                while c2 > left
                    invariant
                        rows == matrix.len(),
                        cols == matrix[0].len(),
                        1 <= rows <= 10,
                        1 <= cols <= 10,
                        top == layer_top + 1,
                        bottom == layer_bottom,
                        left == layer_left,
                        right == layer_right - 1,
                        0 <= left <= c2 <= right <= cols,
                        0 <= top < bottom <= rows,
                        forall |rr: int| 0 <= rr < rows ==> #[trigger] matrix[rr].len() == cols,
                        result@ == after_right + Self::rev_row_segment(matrix@, layer_bottom as int - 1, c2 as int, right as int),
                    decreases c2 - left,
                {
                    c2 -= 1;
                    proof {
                        assert(bottom > 0);
                        assert(bottom - 1 < rows);
                        assert(c2 < right);
                        assert(right <= cols);
                        assert(matrix[(bottom - 1) as int].len() == cols);
                    }
                    let ghost prev = result@;
                    let v = matrix[bottom - 1][c2];
                    result.push(v);
                    proof {
                        assert(prev == after_right + Self::rev_row_segment(matrix@, layer_bottom as int - 1, c2 as int + 1, right as int));
                        assert(result@ == prev.push(v));
                        Self::lemma_rev_row_segment_extend(matrix@, layer_bottom as int - 1, c2 as int, right as int);
                    }
                }
                bottom -= 1;
            }

            let ghost after_bottom = result@;
            if left < right {
                let mut r2: usize = bottom;
                while r2 > top
                    invariant
                        rows == matrix.len(),
                        cols == matrix[0].len(),
                        1 <= rows <= 10,
                        1 <= cols <= 10,
                        top == layer_top + 1,
                        left == layer_left,
                        right == layer_right - 1,
                        0 <= top <= r2 <= bottom <= rows,
                        0 <= left < right <= cols,
                        forall |rr: int| 0 <= rr < rows ==> #[trigger] matrix[rr].len() == cols,
                        result@ == after_bottom + Self::rev_col_segment(matrix@, layer_left as int, r2 as int, bottom as int),
                    decreases r2 - top,
                {
                    r2 -= 1;
                    proof {
                        assert(r2 < rows);
                        assert(left < cols);
                        assert(matrix[r2 as int].len() == cols);
                    }
                    let ghost prev = result@;
                    let v = matrix[r2][left];
                    result.push(v);
                    proof {
                        assert(prev == after_bottom + Self::rev_col_segment(matrix@, layer_left as int, r2 as int + 1, bottom as int));
                        assert(result@ == prev.push(v));
                        Self::lemma_rev_col_segment_extend(matrix@, layer_left as int, r2 as int, bottom as int);
                    }
                }
                left += 1;
            }

            proof {
                assert(base + Self::spiral_region(matrix@, layer_top as int, layer_bottom as int, layer_left as int, layer_right as int) == full);
                if layer_top + 1 < layer_bottom {
                    assert(after_bottom == after_right + Self::rev_row_segment(matrix@, layer_bottom as int - 1, layer_left as int, layer_right as int - 1));
                } else {
                    assert(after_bottom == after_right);
                }
                if layer_left + 1 < layer_right && layer_top + 1 < layer_bottom {
                    assert(result@ == after_bottom + Self::rev_col_segment(matrix@, layer_left as int, layer_top as int + 1, layer_bottom as int - 1));
                } else {
                    assert(result@ == after_bottom);
                }
                assert(result@ == base + Self::layer_seq(matrix@, layer_top as int, layer_bottom as int, layer_left as int, layer_right as int));
                assert(Self::spiral_region(matrix@, layer_top as int, layer_bottom as int, layer_left as int, layer_right as int)
                    == Self::layer_seq(matrix@, layer_top as int, layer_bottom as int, layer_left as int, layer_right as int)
                        + if layer_top + 1 < layer_bottom && layer_left + 1 < layer_right {
                            Self::spiral_region(matrix@, layer_top as int + 1, layer_bottom as int - 1, layer_left as int + 1, layer_right as int - 1)
                        } else {
                            Seq::<i32>::empty()
                        });
                if layer_top + 1 >= layer_bottom {
                    assert(top as int >= bottom as int);
                    assert(Self::spiral_region(matrix@, top as int, bottom as int, left as int, right as int) == Seq::<i32>::empty());
                } else if layer_left + 1 >= layer_right {
                    assert(left as int >= right as int);
                    assert(Self::spiral_region(matrix@, top as int, bottom as int, left as int, right as int) == Seq::<i32>::empty());
                } else {
                    assert(top == layer_top + 1);
                    assert(bottom == layer_bottom - 1);
                    assert(left == layer_left + 1);
                    assert(right == layer_right - 1);
                }
                if layer_top + 1 < layer_bottom && layer_left + 1 < layer_right {
                    assert(Self::spiral_region(matrix@, top as int, bottom as int, left as int, right as int)
                        == Self::spiral_region(matrix@, layer_top as int + 1, layer_bottom as int - 1, layer_left as int + 1, layer_right as int - 1));
                } else {
                    assert(Self::spiral_region(matrix@, top as int, bottom as int, left as int, right as int) == Seq::<i32>::empty());
                }
                assert(result@ + Self::spiral_region(matrix@, top as int, bottom as int, left as int, right as int) == full);
            }
        }

        result
    }
}

}
