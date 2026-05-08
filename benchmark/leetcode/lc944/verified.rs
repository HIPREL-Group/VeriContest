use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn col_inversion(strs: Seq<String>, row: int, col: int) -> bool {
        strs[row - 1]@[col] > strs[row]@[col]
    }

    pub open spec fn col_bad(strs: Seq<String>, col: int) -> bool {
        exists |row: int| 1 <= row < strs.len() && #[trigger] Self::col_inversion(strs, row, col)
    }

    pub open spec fn bad_cols_prefix(strs: Seq<String>, cols: int) -> int
        decreases cols,
    {
        if cols <= 0 {
            0
        } else {
            Self::bad_cols_prefix(strs, cols - 1) + (if Self::col_bad(strs, cols - 1) { 1int } else { 0int })
        }
    }

    pub fn min_deletion_size(strs: Vec<String>) -> (res: i32)
        requires
            1 <= strs.len() <= 100,
            1 <= strs[0]@.len() <= 1000,
            forall |i: int| 0 <= i < strs.len() ==> #[trigger] strs[i]@.len() == strs[0]@.len(),
            forall |i: int, j: int| 0 <= i < strs.len() && 0 <= j < strs[i]@.len() ==>
                'a' <= #[trigger] strs[i]@[j] <= 'z',
        ensures
            0 <= res <= strs[0]@.len(),
            res as int == Self::bad_cols_prefix(strs@, strs[0]@.len() as int),
    {
        let rows = strs.len();
        let cols = strs[0].as_str().unicode_len();
        let mut deleted = 0;
        let mut col: usize = 0;

        while col < cols
            invariant
                rows == strs.len(),
                cols == strs[0]@.len(),
                1 <= rows <= 100,
                1 <= cols <= 1000,
                0 <= col <= cols,
                0 <= deleted <= col,
                forall |i: int| 0 <= i < rows ==> #[trigger] strs[i]@.len() == cols,
                forall |i: int, j: int| 0 <= i < rows && 0 <= j < cols ==> 'a' <= #[trigger] strs[i]@[j] <= 'z',
                deleted as int == Self::bad_cols_prefix(strs@, col as int),
            decreases cols - col,
        {
            let mut bad = false;
            let mut witness: usize = 1;
            let mut row: usize = 1;

            while row < rows
                invariant
                    rows == strs.len(),
                    cols == strs[0]@.len(),
                    1 <= rows <= 100,
                    1 <= cols <= 1000,
                    1 <= row <= rows,
                    0 <= col < cols,
                    1 <= witness <= rows,
                    forall |i: int| 0 <= i < rows ==> #[trigger] strs[i]@.len() == cols,
                    forall |i: int, j: int| 0 <= i < rows && 0 <= j < cols ==> 'a' <= #[trigger] strs[i]@[j] <= 'z',
                    bad ==> 1 <= witness < row && Self::col_inversion(strs@, witness as int, col as int),
                    !bad ==> forall |r: int| 1 <= r < row ==> !Self::col_inversion(strs@, r, col as int),
                decreases rows - row,
            {
                if strs[row - 1].as_str().get_char(col) > strs[row].as_str().get_char(col) {
                    bad = true;
                    witness = row;
                }
                row += 1;
            }

            proof {
                assert(bad <==> Self::col_bad(strs@, col as int)) by {
                    if bad {
                        let r = witness as int;
                        assert(1 <= r < rows);
                        assert(Self::col_inversion(strs@, r, col as int));
                    }
                    if Self::col_bad(strs@, col as int) {
                        let r = choose |r: int| 1 <= r < strs.len() && Self::col_inversion(strs@, r, col as int);
                        assert(1 <= r < row);
                    }
                }
            }

            if bad {
                deleted += 1;
            }
            col += 1;
        }

        deleted
    }
}

}
