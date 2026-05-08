use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn valid_inputs(stairs: Seq<i64>, widths: Seq<usize>, heights: Seq<i64>) -> bool {
    &&& 1 <= stairs.len() <= 100_000
    &&& 1 <= widths.len() <= 100_000
    &&& widths.len() == heights.len()
    &&& forall|i: int| 0 <= i < stairs.len() ==> 1 <= #[trigger] stairs[i] <= 1_000_000_000
    &&& forall|i: int, j: int| 0 <= i < j < stairs.len() ==> stairs[i] <= stairs[j]
    &&& forall|i: int| 0 <= i < widths.len() ==> 1 <= #[trigger] (widths[i] as int) <= stairs.len()
    &&& forall|i: int| 0 <= i < heights.len() ==> 1 <= #[trigger] heights[i] <= 1_000_000_000
}

pub open spec fn top_after(stairs: Seq<i64>, widths: Seq<usize>, heights: Seq<i64>, count: int) -> int
    recommends
        valid_inputs(stairs, widths, heights),
        0 <= count <= widths.len(),
    decreases count,
{
    if count <= 0 {
        0
    } else {
        let idx = count - 1;
        let prev = top_after(stairs, widths, heights, idx);
        let stair = stairs[widths[idx] as int - 1] as int;
        (if stair >= prev { stair } else { prev }) + heights[idx] as int
    }
}

pub open spec fn landing_height(stairs: Seq<i64>, widths: Seq<usize>, heights: Seq<i64>, k: int) -> int
    recommends
        valid_inputs(stairs, widths, heights),
        0 <= k < widths.len(),
{
    let prev = top_after(stairs, widths, heights, k);
    let stair = stairs[widths[k] as int - 1] as int;
    if stair >= prev {
        stair
    } else {
        prev
    }
}

impl Solution {
    pub fn landing_heights(stairs: Vec<i64>, widths: Vec<usize>, heights: Vec<i64>) -> (res: Vec<i64>)
        requires
            valid_inputs(stairs@, widths@, heights@),
        ensures
            res.len() == widths.len(),
            forall|k: int| 0 <= k < res.len() ==> res[k] as int == landing_height(stairs@, widths@, heights@, k),
    {
    }
}

}
