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

    

    proof fn prefix_max_ge(h: Seq<i32>, i: int)
        requires 0 <= i < h.len(),
        ensures Self::prefix_max(h, i) >= h[i] as int,
        decreases i,
    {
        if i > 0 {
            Self::prefix_max_ge(h, i - 1);
        }
    }

    proof fn suffix_max_ge(h: Seq<i32>, i: int)
        requires 0 <= i < h.len(),
        ensures Self::suffix_max(h, i) >= h[i] as int,
        decreases h.len() - i,
    {
        if i < h.len() - 1 {
            Self::suffix_max_ge(h, i + 1);
        }
    }

    proof fn prefix_max_bounded(h: Seq<i32>, i: int, bound: int)
        requires
            0 <= i < h.len(),
            forall |k: int| 0 <= k < h.len() ==> #[trigger] h[k] as int <= bound,
        ensures Self::prefix_max(h, i) <= bound,
        decreases i,
    {
        if i > 0 {
            Self::prefix_max_bounded(h, i - 1, bound);
        }
    }

    proof fn suffix_max_bounded(h: Seq<i32>, i: int, bound: int)
        requires
            0 <= i < h.len(),
            forall |k: int| 0 <= k < h.len() ==> #[trigger] h[k] as int <= bound,
        ensures Self::suffix_max(h, i) <= bound,
        decreases h.len() - i,
    {
        if i < h.len() - 1 {
            Self::suffix_max_bounded(h, i + 1, bound);
        }
    }

    proof fn prefix_max_nonneg(h: Seq<i32>, i: int)
        requires
            0 <= i < h.len(),
            forall |k: int| 0 <= k < h.len() ==> #[trigger] h[k] as int >= 0,
        ensures Self::prefix_max(h, i) >= 0,
        decreases i,
    {
        if i > 0 {
            Self::prefix_max_nonneg(h, i - 1);
        }
    }

    proof fn suffix_max_nonneg(h: Seq<i32>, i: int)
        requires
            0 <= i < h.len(),
            forall |k: int| 0 <= k < h.len() ==> #[trigger] h[k] as int >= 0,
        ensures Self::suffix_max(h, i) >= 0,
        decreases h.len() - i,
    {
        if i < h.len() - 1 {
            Self::suffix_max_nonneg(h, i + 1);
        }
    }

    proof fn water_at_nonneg(h: Seq<i32>, i: int)
        requires 0 <= i < h.len(),
        ensures Self::water_at(h, i) >= 0,
    {
    }

    proof fn water_at_bounded(h: Seq<i32>, i: int, bound: int)
        requires
            0 <= i < h.len(),
            bound >= 0,
            forall |k: int| 0 <= k < h.len() ==> 0 <= #[trigger] h[k] as int <= bound,
        ensures 0 <= Self::water_at(h, i) <= bound,
    {
        Self::prefix_max_ge(h, i);
        Self::suffix_max_ge(h, i);
        Self::prefix_max_bounded(h, i, bound);
        Self::suffix_max_bounded(h, i, bound);
        Self::prefix_max_nonneg(h, i);
        Self::suffix_max_nonneg(h, i);
    }

    proof fn total_water_nonneg(h: Seq<i32>, i: int)
        requires
            0 <= i <= h.len(),
            h.len() >= 1,
        ensures Self::total_water(h, i) >= 0,
        decreases h.len() - i,
    {
        if i < h.len() {
            Self::water_at_nonneg(h, i);
            Self::total_water_nonneg(h, i + 1);
        }
    }

    proof fn total_water_bounded(h: Seq<i32>, i: int, bound: int)
        requires
            0 <= i <= h.len(),
            h.len() <= 20_000,
            bound >= 0,
            forall |k: int| 0 <= k < h.len() ==> 0 <= #[trigger] h[k] as int <= bound,
        ensures
            0 <= Self::total_water(h, i) <= (h.len() - i) * bound,
        decreases h.len() - i,
    {
        if i >= h.len() {
        } else {
            Self::water_at_bounded(h, i, bound);
            Self::total_water_bounded(h, i + 1, bound);
            assert(bound + (h.len() - i - 1) * bound == (h.len() - i) * bound) by(nonlinear_arith)
                requires bound >= 0, h.len() - i >= 1;
        }
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
            invariant
                n == height.len(),
                1 <= n <= 20_000,
                forall |k: int| 0 <= k < height.len() ==> 0 <= #[trigger] height[k] <= 100_000,
                left_max.len() == i,
                forall |j: int| 0 <= j < i ==> left_max[j] as int == Self::prefix_max(height@, j),
                forall |j: int| 0 <= j < i ==> 0 <= #[trigger] left_max[j] <= 100_000,
        {
            proof {
                Self::prefix_max_bounded(height@, i as int, 100_000);
                Self::prefix_max_nonneg(height@, i as int);
            }
            let prev = left_max[i - 1];
            let val = if height[i] > prev { height[i] } else { prev };
            left_max.push(val);
        }

        
        let mut right_max = Vec::with_capacity(n);
        for i in 0..n
            invariant
                n == height.len(),
                right_max.len() == i,
                forall |j: int| 0 <= j < i ==> right_max[j] == height[j],
        {
            right_max.push(height[i]);
        }

        
        for i in 1..n
            invariant
                n == height.len(),
                1 <= n <= 20_000,
                forall |k: int| 0 <= k < height.len() ==> 0 <= #[trigger] height[k] <= 100_000,
                right_max.len() == n,
                forall |j: int| (n - i) as int <= j < n as int ==>
                    right_max[j] as int == Self::suffix_max(height@, j),
                forall |j: int| 0 <= j < (n - i) as int ==> right_max[j] == height[j],
                forall |j: int| (n - i) as int <= j < n as int ==>
                    0 <= #[trigger] right_max[j] <= 100_000,
        {
            let idx = n - 1 - i;
            proof {
                Self::suffix_max_bounded(height@, idx as int, 100_000);
                Self::suffix_max_nonneg(height@, idx as int);
            }
            if right_max[idx + 1] > right_max[idx] {
                right_max[idx] = right_max[idx + 1];
            }
        }

        
        proof {
            Self::total_water_bounded(height@, 0, 100_000);
            assert(20_000int * 100_000 <= i32::MAX as int) by(nonlinear_arith);
        }

        
        let mut water: i32 = 0;
        for i in 0..n
            invariant
                n == height.len(),
                1 <= n <= 20_000,
                forall |k: int| 0 <= k < height.len() ==> 0 <= #[trigger] height[k] <= 100_000,
                left_max.len() == n,
                right_max.len() == n,
                forall |j: int| 0 <= j < n as int ==>
                    left_max[j] as int == Self::prefix_max(height@, j),
                forall |j: int| 0 <= j < n as int ==>
                    right_max[j] as int == Self::suffix_max(height@, j),
                forall |j: int| 0 <= j < n as int ==> 0 <= #[trigger] left_max[j] <= 100_000,
                forall |j: int| 0 <= j < n as int ==> 0 <= #[trigger] right_max[j] <= 100_000,
                0 <= Self::total_water(height@, 0) <= 20_000int * 100_000,
                20_000int * 100_000 <= i32::MAX as int,
                water as int == Self::total_water(height@, 0) - Self::total_water(height@, i as int),
                0 <= Self::total_water(height@, i as int),
        {
            proof {
                Self::prefix_max_ge(height@, i as int);
                Self::suffix_max_ge(height@, i as int);
                Self::water_at_bounded(height@, i as int, 100_000);
                Self::total_water_nonneg(height@, (i + 1) as int);
                
                assert(Self::total_water(height@, i as int) ==
                    Self::water_at(height@, i as int) + Self::total_water(height@, (i + 1) as int));
            }
            let min_max = if left_max[i] < right_max[i] { left_max[i] } else { right_max[i] };
            water += min_max - height[i];
        }

        water
    }
}

} 
