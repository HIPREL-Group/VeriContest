use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn min_cost_piece(horizontal: int, vertical: Seq<i32>, end: int) -> int
        recommends
            0 <= end <= vertical.len(),
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::min_cost_piece(horizontal, vertical, end - 1)
                + if horizontal <= vertical[end - 1] as int {
                    horizontal
                } else {
                    vertical[end - 1] as int
                }
        }
    }

    pub open spec fn cross_cost(horizontal: Seq<i32>, h_end: int, vertical: Seq<i32>) -> int
        recommends
            0 <= h_end <= horizontal.len(),
        decreases h_end,
    {
        if h_end <= 0 {
            0
        } else {
            Self::cross_cost(horizontal, h_end - 1, vertical)
                + Self::min_cost_piece(horizontal[h_end - 1] as int, vertical, vertical.len() as int)
        }
    }

    pub open spec fn sum_prefix(values: Seq<i32>, end: int) -> int
        recommends
            0 <= end <= values.len(),
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::sum_prefix(values, end - 1) + values[end - 1] as int
        }
    }

    pub open spec fn exact_cost(horizontal: Seq<i32>, vertical: Seq<i32>) -> int {
        Self::sum_prefix(horizontal, horizontal.len() as int)
            + Self::sum_prefix(vertical, vertical.len() as int)
            + Self::cross_cost(horizontal, horizontal.len() as int, vertical)
    }

    pub open spec fn minimum_cost_spec(m: i32, n: i32, horizontal_cut: Seq<i32>, vertical_cut: Seq<i32>, result: int) -> bool {
        &&& 1 <= m <= 20
        &&& 1 <= n <= 20
        &&& horizontal_cut.len() == m - 1
        &&& vertical_cut.len() == n - 1
        &&& forall |i: int| 0 <= i < horizontal_cut.len() ==> 1 <= #[trigger] horizontal_cut[i] <= 1000
        &&& forall |j: int| 0 <= j < vertical_cut.len() ==> 1 <= #[trigger] vertical_cut[j] <= 1000
        &&& result == Self::exact_cost(horizontal_cut, vertical_cut)
    }

    pub fn minimum_cost(m: i32, n: i32, horizontal_cut: Vec<i32>, vertical_cut: Vec<i32>) -> (result: i32)
        requires
            1 <= m <= 20,
            1 <= n <= 20,
            horizontal_cut.len() == m - 1,
            vertical_cut.len() == n - 1,
            forall |i: int| 0 <= i < horizontal_cut.len() ==> 1 <= #[trigger] horizontal_cut[i] <= 1000,
            forall |j: int| 0 <= j < vertical_cut.len() ==> 1 <= #[trigger] vertical_cut[j] <= 1000,
        ensures
            result as int == Self::exact_cost(horizontal_cut@, vertical_cut@),
    {
    }
}

}
