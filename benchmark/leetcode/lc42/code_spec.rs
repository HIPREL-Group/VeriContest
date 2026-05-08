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
        let n = height.len();

        let mut left_max = Vec::with_capacity(n);
        left_max.push(height[0]);
        for i in 1..n
        {
            let prev = left_max[i - 1];
            let val = if height[i] > prev { height[i] } else { prev };
            left_max.push(val);
        }

        let mut right_max = Vec::with_capacity(n);
        for i in 0..n
        {
            right_max.push(height[i]);
        }
        for i in 1..n
        {
            let idx = n - 1 - i;
            if right_max[idx + 1] > right_max[idx] {
                right_max[idx] = right_max[idx + 1];
            }
        }

        let mut water: i32 = 0;
        for i in 0..n
        {
            let min_max = if left_max[i] < right_max[i] { left_max[i] } else { right_max[i] };
            water += min_max - height[i];
        }

        water
    }
}

}
