use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn prefix_max(h: Seq<i32>, i: int) -> int
        decreases i
    {
        if i <= 0 { h[0] as int }
        else {
            let prev = Self::prefix_max(h, i - 1);
            if h[i] as int > prev { h[i] as int } else { prev }
        }
    }

    pub open spec fn suffix_max(h: Seq<i32>, i: int) -> int
        decreases h.len() - i
    {
        if i >= h.len() - 1 { h[h.len() - 1] as int }
        else {
            let next = Self::suffix_max(h, i + 1);
            if h[i] as int > next { h[i] as int } else { next }
        }
    }

    pub open spec fn water_at(h: Seq<i32>, i: int) -> int {
        let pm = Self::prefix_max(h, i);
        let sm = Self::suffix_max(h, i);
        let min_max = if pm < sm { pm } else { sm };
        if min_max - h[i] as int > 0 { min_max - h[i] as int } else { 0 }
    }

    pub open spec fn total_water(h: Seq<i32>, i: int) -> int
        decreases h.len() - i
    {
        if i >= h.len() { 0 }
        else { Self::water_at(h, i) + Self::total_water(h, i + 1) }
    }

    pub fn trap(height: Vec<i32>) -> (result: i32)
        requires
            1 <= height.len() <= 20_000,
            forall |i: int| 0 <= i < height.len() ==> 0 <= #[trigger] height[i] <= 100_000,
        ensures
            result as int == Self::total_water(height@, 0),
    {
    }
}

}
