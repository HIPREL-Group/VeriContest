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

proof fn lemma_top_after_step(stairs: Seq<i64>, widths: Seq<usize>, heights: Seq<i64>, count: int)
    requires
        valid_inputs(stairs, widths, heights),
        0 <= count < widths.len(),
    ensures
        top_after(stairs, widths, heights, count + 1) == landing_height(stairs, widths, heights, count) + heights[count] as int,
{
    reveal_with_fuel(top_after, 2);
    reveal_with_fuel(landing_height, 1);
}

impl Solution {
    pub fn landing_heights(stairs: Vec<i64>, widths: Vec<usize>, heights: Vec<i64>) -> (res: Vec<i64>)
        requires
            valid_inputs(stairs@, widths@, heights@),
        ensures
            res.len() == widths.len(),
            forall|k: int| 0 <= k < res.len() ==> res[k] as int == landing_height(stairs@, widths@, heights@, k),
    {
        let mut res = Vec::new();
        let mut current_top = 0i64;
        let mut i = 0usize;
        while i < widths.len()
            invariant
                valid_inputs(stairs@, widths@, heights@),
                0 <= i <= widths.len(),
                res.len() == i,
                current_top as int == top_after(stairs@, widths@, heights@, i as int),
                0 <= current_top as int <= stairs[stairs.len() as int - 1] as int + i as int * 1_000_000_000,
                forall|k: int| 0 <= k < i as int ==> res[k] as int == landing_height(stairs@, widths@, heights@, k),
            decreases widths.len() - i,
        {
            proof {
                assert(1 <= widths[i as int] as int <= stairs.len());
                assert(1 <= heights[i as int] <= 1_000_000_000);
            }
            let w = widths[i];
            let stair = stairs[w - 1];
            let base = if stair >= current_top { stair } else { current_top };
            proof {
                reveal_with_fuel(landing_height, 1);
                assert(base as int == landing_height(stairs@, widths@, heights@, i as int));
                if stair >= current_top {
                    assert(stair as int >= top_after(stairs@, widths@, heights@, i as int));
                } else {
                    assert(top_after(stairs@, widths@, heights@, i as int) > stair as int);
                }
            }
            let ghost old_res = res@;
            res.push(base);
            current_top = base + heights[i];
            proof {
                lemma_top_after_step(stairs@, widths@, heights@, i as int);
                assert(res@ == old_res.push(base));
                assert(current_top as int == top_after(stairs@, widths@, heights@, i as int + 1));
                assert(base as int <= stairs[stairs.len() as int - 1] as int + i as int * 1_000_000_000);
                assert(current_top as int <= stairs[stairs.len() as int - 1] as int + i as int * 1_000_000_000 + 1_000_000_000);
                assert(current_top as int <= stairs[stairs.len() as int - 1] as int + (i as int + 1) * 1_000_000_000);
                assert forall|k: int| 0 <= k < i as int + 1 implies res[k] as int == landing_height(stairs@, widths@, heights@, k) by {
                    if k < i as int {
                        assert(res[k] == old_res[k]);
                    } else {
                        assert(k == i as int);
                    }
                }
            }
            i += 1;
        }
        proof {
            assert(i == widths.len());
        }
        res
    }
}

}
