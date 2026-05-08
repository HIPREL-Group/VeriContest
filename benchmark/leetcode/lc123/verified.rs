use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    

    pub open spec fn spec_max(a: int, b: int) -> int {
        if a >= b { a } else { b }
    }

    pub open spec fn min_prefix(prices: Seq<i32>, i: int) -> int
        decreases i
    {
        if i <= 0 { prices[0] as int }
        else {
            let rest = Self::min_prefix(prices, i - 1);
            if (prices[i] as int) < rest { prices[i] as int } else { rest }
        }
    }

    pub open spec fn forward_max(prices: Seq<i32>, i: int) -> int
        decreases i
    {
        if i <= 0 { 0 }
        else {
            let sell_today = prices[i] as int - Self::min_prefix(prices, i);
            let prev = Self::forward_max(prices, i - 1);
            if sell_today > prev { sell_today } else { prev }
        }
    }

    pub open spec fn max_suffix(prices: Seq<i32>, i: int) -> int
        decreases prices.len() - i
    {
        if i >= prices.len() - 1 { prices[prices.len() as int - 1] as int }
        else {
            let rest = Self::max_suffix(prices, i + 1);
            if (prices[i] as int) > rest { prices[i] as int } else { rest }
        }
    }

    pub open spec fn backward_max(prices: Seq<i32>, i: int) -> int
        decreases prices.len() - i
    {
        if i >= prices.len() - 1 { 0 }
        else {
            let buy_today = Self::max_suffix(prices, i) - prices[i] as int;
            let next = Self::backward_max(prices, i + 1);
            if buy_today > next { buy_today } else { next }
        }
    }

    pub open spec fn best_combined(prices: Seq<i32>, k: int) -> int
        decreases prices.len() - k
    {
        if k >= prices.len() { 0 }
        else {
            let here = Self::forward_max(prices, k) + Self::backward_max(prices, k);
            let rest = Self::best_combined(prices, k + 1);
            if here > rest { here } else { rest }
        }
    }

    

    proof fn min_prefix_bounded(prices: Seq<i32>, i: int)
        requires
            0 <= i < prices.len(),
            forall |k: int| 0 <= k < prices.len() ==> 0 <= #[trigger] prices[k] as int <= 100_000,
        ensures 0 <= Self::min_prefix(prices, i) <= 100_000,
        decreases i,
    {
        if i > 0 { Self::min_prefix_bounded(prices, i - 1); }
    }

    proof fn min_prefix_le(prices: Seq<i32>, i: int)
        requires 0 <= i < prices.len(),
        ensures Self::min_prefix(prices, i) <= prices[i] as int,
        decreases i,
    {
        if i > 0 { Self::min_prefix_le(prices, i - 1); }
    }

    proof fn forward_max_bounded(prices: Seq<i32>, i: int)
        requires
            0 <= i < prices.len(),
            forall |k: int| 0 <= k < prices.len() ==> 0 <= #[trigger] prices[k] as int <= 100_000,
        ensures 0 <= Self::forward_max(prices, i) <= 100_000,
        decreases i,
    {
        if i > 0 {
            Self::forward_max_bounded(prices, i - 1);
            Self::min_prefix_bounded(prices, i);
            Self::min_prefix_le(prices, i);
        }
    }

    proof fn max_suffix_bounded(prices: Seq<i32>, i: int)
        requires
            0 <= i < prices.len(),
            forall |k: int| 0 <= k < prices.len() ==> 0 <= #[trigger] prices[k] as int <= 100_000,
        ensures 0 <= Self::max_suffix(prices, i) <= 100_000,
        decreases prices.len() - i,
    {
        if i < prices.len() - 1 { Self::max_suffix_bounded(prices, i + 1); }
    }

    proof fn max_suffix_ge(prices: Seq<i32>, i: int)
        requires 0 <= i < prices.len(),
        ensures Self::max_suffix(prices, i) >= prices[i] as int,
        decreases prices.len() - i,
    {
        if i < prices.len() - 1 { Self::max_suffix_ge(prices, i + 1); }
    }

    proof fn backward_max_bounded(prices: Seq<i32>, i: int)
        requires
            0 <= i < prices.len(),
            forall |k: int| 0 <= k < prices.len() ==> 0 <= #[trigger] prices[k] as int <= 100_000,
        ensures 0 <= Self::backward_max(prices, i) <= 100_000,
        decreases prices.len() - i,
    {
        if i < prices.len() - 1 {
            Self::backward_max_bounded(prices, i + 1);
            Self::max_suffix_bounded(prices, i);
            Self::max_suffix_ge(prices, i);
        }
    }

    proof fn best_combined_bounded(prices: Seq<i32>, k: int)
        requires
            0 <= k,
            prices.len() >= 1,
            forall |j: int| 0 <= j < prices.len() ==> 0 <= #[trigger] prices[j] as int <= 100_000,
        ensures 0 <= Self::best_combined(prices, k) <= 200_000,
        decreases prices.len() - k,
    {
        if k < prices.len() {
            Self::forward_max_bounded(prices, k);
            Self::backward_max_bounded(prices, k);
            Self::best_combined_bounded(prices, k + 1);
        }
    }

    

    pub fn max_profit(prices: Vec<i32>) -> (result: i32)
        requires
            1 <= prices.len() <= 100_000,
            forall |i: int| 0 <= i < prices.len() ==> 0 <= #[trigger] prices[i] <= 100_000,
        ensures
            result >= 0,
            result as int == Self::best_combined(prices@, 0),
    {
        let n = prices.len();
        let ghost p = prices@;

        
        let mut forward: Vec<i32> = Vec::with_capacity(n);
        forward.push(0i32);
        let mut min_price = prices[0];

        for i in 1..n
            invariant
                n == prices.len(),
                1 <= n <= 100_000,
                p == prices@,
                forall |k: int| 0 <= k < n ==> 0 <= #[trigger] prices[k] <= 100_000,
                forward.len() == i,
                0 <= min_price <= 100_000,
                min_price as int == Self::min_prefix(p, (i - 1) as int),
                forall |j: int| 0 <= j < i ==> forward[j] as int == Self::forward_max(p, j),
                forall |j: int| 0 <= j < i ==> 0 <= #[trigger] forward[j] <= 100_000,
        {
            proof {
                Self::min_prefix_bounded(p, i as int);
                Self::min_prefix_le(p, i as int);
                Self::forward_max_bounded(p, i as int);
                
                assert(forward[(i - 1) as int] as int == Self::forward_max(p, (i - 1) as int));
            }
            if prices[i] < min_price { min_price = prices[i]; }
            assert(min_price as int == Self::min_prefix(p, i as int));
            let profit = prices[i] - min_price;
            let prev = forward[i - 1];
            let val = if profit > prev { profit } else { prev };
            forward.push(val);
        }

        
        let mut backward: Vec<i32> = Vec::with_capacity(n);
        for i in 0..n
            invariant
                backward.len() == i,
                forall |j: int| 0 <= j < i ==> backward[j] == 0i32,
        {
            backward.push(0i32);
        }

        
        let mut max_price = prices[n - 1];

        proof {
            
            assert(Self::backward_max(p, (n - 1) as int) == 0);
            assert(backward[(n - 1) as int] == 0i32);
        }

        for i in 1..n
            invariant
                n == prices.len(),
                1 <= n <= 100_000,
                p == prices@,
                forall |k: int| 0 <= k < n ==> 0 <= #[trigger] prices[k] <= 100_000,
                backward.len() == n,
                0 <= max_price <= 100_000,
                max_price as int == Self::max_suffix(p, (n - i) as int),
                forall |j: int| (n - i) as int <= j < n as int
                    ==> backward[j] as int == Self::backward_max(p, j),
                forall |j: int| (n - i) as int <= j < n as int
                    ==> 0 <= #[trigger] backward[j] <= 100_000,
        {
            let idx = n - 1 - i;
            proof {
                Self::max_suffix_bounded(p, idx as int);
                Self::max_suffix_ge(p, idx as int);
                Self::backward_max_bounded(p, idx as int);
                
                assert(backward[(idx + 1) as int] as int == Self::backward_max(p, (idx + 1) as int));
            }
            if prices[idx] > max_price { max_price = prices[idx]; }
            assert(max_price as int == Self::max_suffix(p, idx as int));
            let profit = max_price - prices[idx];
            let next = backward[idx + 1];
            let val = if profit > next { profit } else { next };
            backward.set(idx, val);
        }

        
        proof {
            Self::best_combined_bounded(p, 0);
        }

        let mut res: i32 = 0;

        for i in 0..n
            invariant
                n == prices.len(),
                1 <= n <= 100_000,
                p == prices@,
                forall |k: int| 0 <= k < n ==> 0 <= #[trigger] prices[k] <= 100_000,
                forward.len() == n,
                backward.len() == n,
                forall |j: int| 0 <= j < n as int
                    ==> forward[j] as int == Self::forward_max(p, j),
                forall |j: int| 0 <= j < n as int
                    ==> backward[j] as int == Self::backward_max(p, j),
                forall |j: int| 0 <= j < n as int
                    ==> 0 <= #[trigger] forward[j] <= 100_000,
                forall |j: int| 0 <= j < n as int
                    ==> 0 <= #[trigger] backward[j] <= 100_000,
                0 <= i <= n,
                0 <= res <= 200_000,
                0 <= Self::best_combined(p, 0) <= 200_000,
                Self::spec_max(res as int, Self::best_combined(p, i as int))
                    == Self::best_combined(p, 0),
        {
            proof {
                Self::forward_max_bounded(p, i as int);
                Self::backward_max_bounded(p, i as int);
                Self::best_combined_bounded(p, (i + 1) as int);
                
                assert(Self::best_combined(p, i as int)
                    == Self::spec_max(
                        Self::forward_max(p, i as int) + Self::backward_max(p, i as int),
                        Self::best_combined(p, (i + 1) as int)));
            }
            let total = forward[i] + backward[i];
            if total > res { res = total; }
        }

        res
    }
}

} 
