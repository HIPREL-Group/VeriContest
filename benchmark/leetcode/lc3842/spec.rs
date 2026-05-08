use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn bulb_on_prefix(bulbs: Seq<i32>, end: nat, bulb: int) -> bool
        recommends
            end <= bulbs.len(),
        decreases end,
    {
        if end == 0 {
            false
        } else if bulbs[end as int - 1] as int == bulb {
            !Self::bulb_on_prefix(bulbs, (end - 1) as nat, bulb)
        } else {
            Self::bulb_on_prefix(bulbs, (end - 1) as nat, bulb)
        }
    }

    pub fn toggle_light_bulbs(bulbs: Vec<i32>) -> (res: Vec<i32>)
        requires
            1 <= bulbs.len() <= 100,
            forall|i: int| 0 <= i < bulbs.len() ==> 1 <= #[trigger] bulbs[i] <= 100,
        ensures
            forall|i: int| 0 <= i < res.len() ==> 1 <= #[trigger] res[i] as int && res[i] as int <= 100,
            forall|i: int, j: int| 0 <= i < j < res.len() ==> res[i] < res[j],
            forall|b: int| 1 <= b <= 100 ==> (
                (exists|k: int| 0 <= k < res.len() && #[trigger] res[k] as int == b)
                    <==> Self::bulb_on_prefix(bulbs@, bulbs.len() as nat, b)
            ),
    {
    }
}

} 
