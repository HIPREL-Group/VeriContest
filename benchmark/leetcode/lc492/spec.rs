use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn scan_spec(area: nat, w: nat, best_w: nat) -> nat
        recommends
            1 <= w,
            1 <= best_w < w,
            area % best_w == 0,
            area / best_w >= best_w,
        decreases area + 1 - w,
    {
        if w > area {
            best_w
        } else if area % w == 0 && area / w >= w {
            Self::scan_spec(area, w + 1, w)
        } else {
            Self::scan_spec(area, w + 1, best_w)
        }
    }

    pub open spec fn construct_rectangle_spec(area: nat) -> (nat, nat) {
        let w = Self::scan_spec(area, 1, 1);
        (area / w, w)
    }

    pub fn construct_rectangle(area: i32) -> (res: Vec<i32>)
        requires
            1 <= area <= 10_000_000,
        ensures
            res.len() == 2,
            res[0] as nat == Self::construct_rectangle_spec(area as nat).0,
            res[1] as nat == Self::construct_rectangle_spec(area as nat).1,
    {
    }
}

} 
