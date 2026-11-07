use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn abs_spec(x: int) -> int {
        if x >= 0 { x } else { -x }
    }

    pub open spec fn dist_spec(r: int, c: int, rc: int, cc: int) -> int {
        Self::abs_spec(r - rc) + Self::abs_spec(c - cc)
    }

    pub open spec fn cell_covered(result: Seq<Vec<i32>>, r: int, c: int) -> bool {
        exists|k: int| 0 <= k < result.len() && result[k][0] as int == r && result[k][1] as int == c
    }

    pub fn all_cells_dist_order(rows: i32, cols: i32, r_center: i32, c_center: i32) -> (result: Vec<Vec<i32>>)
        requires
            1 <= rows <= 100,
            1 <= cols <= 100,
            0 <= r_center < rows,
            0 <= c_center < cols,
        ensures
            result@.len() == rows as int * cols as int,
            forall|i: int| 0 <= i < result@.len() ==> (#[trigger] result@[i]).len() == 2,
            forall|i: int| #![trigger result@[i]] 0 <= i < result@.len() ==>
                0 <= result@[i][0] < rows && 0 <= result@[i][1] < cols,
            forall|i: int| #![trigger result@[i]] 0 <= i < result@.len() - 1 ==>
                Self::dist_spec(
                    result@[i][0] as int, result@[i][1] as int,
                    r_center as int, c_center as int,
                ) <= Self::dist_spec(
                    result@[i + 1][0] as int, result@[i + 1][1] as int,
                    r_center as int, c_center as int,
                ),
            forall|r: int, c: int| 0 <= r < rows as int && 0 <= c < cols as int ==>
                (#[trigger] Self::cell_covered(result@, r, c)),
    {
        let max_r_dist = if r_center > rows - 1 - r_center { r_center } else { rows - 1 - r_center };
        let max_c_dist = if c_center > cols - 1 - c_center { c_center } else { cols - 1 - c_center };
        let max_dist = max_r_dist + max_c_dist;
        let mut result: Vec<Vec<i32>> = Vec::new();
        let mut d: i32 = 0;
        while d <= max_dist {
            let mut r: i32 = 0;
            while r < rows {
                let mut c: i32 = 0;
                while c < cols {
                    let rd = if r >= r_center { r - r_center } else { r_center - r };
                    let cd = if c >= c_center { c - c_center } else { c_center - c };
                    if rd + cd == d {
                        let mut cell: Vec<i32> = Vec::new();
                        cell.push(r);
                        cell.push(c);
                        result.push(cell);
                    }
                    c = c + 1;
                }
                r = r + 1;
            }
            d = d + 1;
        }
        result
    }
}

}
