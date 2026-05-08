use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn run_length(prices: Seq<i32>, i: int) -> int
    decreases i,
{
    if i <= 0 {
        1
    } else if i >= prices.len() {
        0
    } else if prices[i - 1] - prices[i] == 1 {
        run_length(prices, i - 1) + 1
    } else {
        1
    }
}

pub open spec fn total_periods(prices: Seq<i32>, n: int) -> int
    decreases n,
{
    if n <= 0 {
        0
    } else {
        total_periods(prices, n - 1) + run_length(prices, n - 1)
    }
}

proof fn run_length_bounds(prices: Seq<i32>, i: int)
    requires
        0 <= i < prices.len(),
    ensures
        1 <= run_length(prices, i) <= i + 1,
    decreases i,
{
    if i <= 0 {
        
    } else if prices[i - 1] - prices[i] == 1 {
        run_length_bounds(prices, i - 1);
    } else {
        
    }
}

proof fn total_periods_bounds(prices: Seq<i32>, n: int)
    requires
        0 <= n <= prices.len(),
        n <= 100_000,
    ensures
        0 <= total_periods(prices, n),
        total_periods(prices, n) <= n * (n + 1) / 2,
    decreases n,
{
    if n <= 0 {
        
    } else {
        total_periods_bounds(prices, n - 1);
        run_length_bounds(prices, n - 1);
        assert(total_periods(prices, n) == total_periods(prices, n - 1) + run_length(prices, n - 1));
        assert(total_periods(prices, n) >= 0) by (nonlinear_arith)
            requires
                total_periods(prices, n - 1) >= 0,
                run_length(prices, n - 1) >= 1,
                total_periods(prices, n) == total_periods(prices, n - 1) + run_length(prices, n - 1),
        {}
        assert(total_periods(prices, n) <= n * (n + 1) / 2) by (nonlinear_arith)
            requires
                total_periods(prices, n - 1) <= (n - 1) * n / 2,
                run_length(prices, n - 1) <= n,
                total_periods(prices, n) == total_periods(prices, n - 1) + run_length(prices, n - 1),
        {}
    }
}

impl Solution {
    pub fn get_descent_periods(prices: Vec<i32>) -> (total: i64)
        requires
            1 <= prices.len() <= 100_000,
            forall |i: int| 0 <= i < prices.len() ==> 1 <= #[trigger] prices[i] <= 100_000,
        ensures
            total == total_periods(prices@, prices.len() as int),
    {
        let n = prices.len();
        let mut total: i64 = 0;
        let mut run_len: i64 = 0;
        let mut i: usize = 0;
        while i < n
            invariant
                n == prices.len(),
                1 <= n <= 100_000,
                forall |k: int| 0 <= k < prices.len() ==> 1 <= #[trigger] prices[k] <= 100_000,
                0 <= i <= n,
                i > 0 ==> run_len == run_length(prices@, (i - 1) as int),
                i == 0 ==> run_len == 0,
                i > 0 ==> 1 <= run_len <= i as i64,
                total == total_periods(prices@, i as int),
                0 <= total <= i as i64 * (i as i64 + 1) / 2,
            decreases n - i,
        {
            if i > 0 && prices[i - 1] - prices[i] == 1 {
                run_len += 1;
            } else {
                run_len = 1;
            }

            proof {
                
                assert(run_len == run_length(prices@, i as int));
                run_length_bounds(prices@, i as int);
            }

            
            
            
            assert(total + run_len <= 5_000_050_001i64) by (nonlinear_arith)
                requires
                    0 <= total <= (i as i64) * (i as i64 + 1) / 2,
                    1 <= run_len <= i as i64 + 1,
                    (i as i64) < 100_000i64,
            {}

            total += run_len;

            proof {
                
                assert(total_periods(prices@, (i + 1) as int) == 
                       total_periods(prices@, i as int) + run_length(prices@, i as int));
                assert(total == total_periods(prices@, (i + 1) as int));
                total_periods_bounds(prices@, (i + 1) as int);
            }

            i += 1;
        }
        total
    }
}

} 
