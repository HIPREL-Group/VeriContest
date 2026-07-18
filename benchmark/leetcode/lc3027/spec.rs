use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn inside(points: Seq<Seq<int>>, i: int, j: int, t: int) -> bool {
        &&& points[i][0] <= points[t][0]
        &&& points[t][0] <= points[j][0]
        &&& points[j][1] <= points[t][1]
        &&& points[t][1] <= points[i][1]
    }

    pub open spec fn valid_pair(points: Seq<Seq<int>>, i: int, j: int) -> bool {
        &&& i != j
        &&& points[i][0] <= points[j][0]
        &&& points[i][1] >= points[j][1]
        &&& (forall|t: int|
            0 <= t < points.len() && t != i && t != j ==> !Self::inside(points, i, j, t))
    }

    pub open spec fn count_j(points: Seq<Seq<int>>, i: int, jend: int) -> int
        decreases jend,
    {
        if jend <= 0 {
            0
        } else {
            Self::count_j(points, i, jend - 1) + (if Self::valid_pair(points, i, jend - 1) {
                1int
            } else {
                0int
            })
        }
    }

    pub open spec fn count_i(points: Seq<Seq<int>>, iend: int) -> int
        decreases iend,
    {
        if iend <= 0 {
            0
        } else {
            Self::count_i(points, iend - 1) + Self::count_j(points, iend - 1, points.len() as int)
        }
    }

    pub open spec fn spec_number_of_pairs(points: Seq<Seq<int>>) -> int {
        Self::count_i(points, points.len() as int)
    }

    pub fn number_of_pairs(points: Vec<Vec<i32>>) -> (result: i32)
        requires
            2 <= points.len() <= 1000,
            forall |i: int| 0 <= i < points.len() ==> #[trigger] points[i].len() == 2,
            forall |i: int| 0 <= i < points.len()
                ==> -1_000_000_000 <= #[trigger] points[i][0] <= 1_000_000_000
                    && -1_000_000_000 <= points[i][1] <= 1_000_000_000,
        ensures
            result as int == Self::spec_number_of_pairs(points@.map_values(|p: Vec<i32>| p@.map_values(|v: i32| v as int))),
    {
    }
}

}