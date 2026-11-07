use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_upper_left(points: Seq<Vec<i32>>, i: int, j: int) -> bool {
        &&& 0 <= i < points.len()
        &&& 0 <= j < points.len()
        &&& points[i][0] <= points[j][0]
        &&& points[i][1] >= points[j][1]
    }

    pub open spec fn blocks(points: Seq<Vec<i32>>, i: int, j: int, k: int) -> bool {
        &&& 0 <= i < points.len()
        &&& 0 <= j < points.len()
        &&& 0 <= k < points.len()
        &&& k != i
        &&& k != j
        &&& points[i][0] <= points[k][0] <= points[j][0]
        &&& points[j][1] <= points[k][1] <= points[i][1]
    }

    pub open spec fn no_block_prefix(points: Seq<Vec<i32>>, i: int, j: int, end: int) -> bool
        decreases end,
    {
        if end <= 0 {
            true
        } else {
            Self::no_block_prefix(points, i, j, end - 1)
                && !Self::blocks(points, i, j, end - 1)
        }
    }

    pub open spec fn valid_pair(points: Seq<Vec<i32>>, i: int, j: int) -> bool {
        &&& i != j
        &&& Self::is_upper_left(points, i, j)
        &&& Self::no_block_prefix(points, i, j, points.len() as int)
    }

    pub open spec fn count_i_prefix(points: Seq<Vec<i32>>, i: int, end_j: int) -> int
        decreases end_j,
    {
        if end_j <= 0 {
            0
        } else {
            Self::count_i_prefix(points, i, end_j - 1)
                + if Self::valid_pair(points, i, end_j - 1) { 1int } else { 0int }
        }
    }

    pub open spec fn number_of_pairs_spec_prefix(points: Seq<Vec<i32>>, end_i: int) -> int
        decreases end_i,
    {
        if end_i <= 0 {
            0
        } else {
            Self::number_of_pairs_spec_prefix(points, end_i - 1)
                + Self::count_i_prefix(points, end_i - 1, points.len() as int)
        }
    }

    pub open spec fn number_of_pairs_spec(points: Seq<Vec<i32>>) -> int {
        Self::number_of_pairs_spec_prefix(points, points.len() as int)
    }

    pub fn number_of_pairs(points: Vec<Vec<i32>>) -> (result: i32)
        requires
            2 <= points.len() <= 50,
            forall |i: int| 0 <= i < points.len() ==> #[trigger] points[i].len() == 2,
            forall |i: int| 0 <= i < points.len() ==> 0 <= #[trigger] points[i][0] <= 50,
            forall |i: int| 0 <= i < points.len() ==> 0 <= #[trigger] points[i][1] <= 50,
            forall |i: int, j: int| 0 <= i < j < points.len() ==> #[trigger] points[i] != #[trigger] points[j],
        ensures
            result as int == Self::number_of_pairs_spec(points@),
    {
        let n = points.len();
        let mut ans: i32 = 0;

        let mut i: usize = 0;
        while i < n {
            let mut j: usize = 0;
            while j < n {
                let mut pair_valid = false;
                if i != j {
                    let x1 = points[i][0];
                    let y1 = points[i][1];
                    let x2 = points[j][0];
                    let y2 = points[j][1];
                    if x1 <= x2 && y1 >= y2 {
                        let mut ok = true;
                        let mut k: usize = 0;
                        while k < n {
                            let mut is_block = false;
                            if k != i && k != j {
                                let x3 = points[k][0];
                                let y3 = points[k][1];
                                if x1 <= x3 && x3 <= x2 && y2 <= y3 && y3 <= y1 {
                                    is_block = true;
                                }
                            }
                            ok = ok && !is_block;
                            k += 1;
                        }
                        pair_valid = ok;
                    }
                }
                let add: i32 = if pair_valid { 1 } else { 0 };
                ans += add;
                j += 1;
            }
            i += 1;
        }

        ans
    }
}

}
