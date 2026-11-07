use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn min2(x: int, y: int) -> int {
    if x < y { x } else { y }
}

pub open spec fn min_suffix_sum(a: Seq<i64>, b: Seq<i64>, start: int, end: int) -> int
    recommends
        0 <= start <= end <= a.len(),
        a.len() == b.len(),
    decreases end - start,
{
    if start >= end {
        0int
    } else {
        min2(a[start] as int, b[start] as int) + min_suffix_sum(a, b, start + 1, end)
    }
}

pub open spec fn cost_at(a: Seq<i64>, b: Seq<i64>, j: int) -> int
    recommends
        0 <= j < a.len(),
        a.len() == b.len(),
{
    a[j] as int + min_suffix_sum(a, b, j + 1, a.len() as int)
}

pub open spec fn min_cost(a: Seq<i64>, b: Seq<i64>, m: int) -> int
    recommends
        1 <= m <= a.len(),
        a.len() == b.len(),
    decreases m,
{
    if m <= 1 {
        cost_at(a, b, 0)
    } else {
        let prev = min_cost(a, b, m - 1);
        let cur = cost_at(a, b, m - 1);
        if cur < prev { cur } else { prev }
    }
}

proof fn lemma_min_suffix_sum_bound(a: Seq<i64>, b: Seq<i64>, start: int, end: int)
    requires
        0 <= start <= end <= a.len(),
        a.len() == b.len(),
        a.len() <= 200_000,
        forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= 1_000_000_000,
        forall|i: int| 0 <= i < b.len() ==> 1 <= #[trigger] b[i] <= 1_000_000_000,
    ensures
        0 <= min_suffix_sum(a, b, start, end) <= (end - start) * 1_000_000_000,
    decreases end - start,
{
    if start >= end {
    } else {
        lemma_min_suffix_sum_bound(a, b, start + 1, end);
        assert(1 <= a[start] <= 1_000_000_000);
        assert(1 <= b[start] <= 1_000_000_000);
        assert(min2(a[start] as int, b[start] as int) <= 1_000_000_000);
        assert(min2(a[start] as int, b[start] as int) >= 1);
    }
}

impl Solution {
    pub fn min_coins(a: Vec<i64>, b: Vec<i64>, m: usize) -> (result: i64)
        requires
            1 <= m <= a.len() <= 200_000,
            a.len() == b.len(),
            forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= 1_000_000_000,
            forall|i: int| 0 <= i < b.len() ==> 1 <= #[trigger] b[i] <= 1_000_000_000,
        ensures
            result as int == min_cost(a@, b@, m as int),
    {
        let n = a.len();
        let ghost na = a@;
        let ghost nb = b@;
        let mut suffix: Vec<i64> = Vec::with_capacity(n + 1);
        let mut k: usize = 0;
        while k <= n
            invariant
                k <= n + 1,
                n <= 200_000,
                suffix.len() == k,
                forall|jj: int| 0 <= jj < (k as int) ==> #[trigger] suffix[jj] == 0i64,
            decreases (n + 1) - k,
        {
            suffix.push(0);
            k = k + 1;
        }
        proof {
            reveal_with_fuel(min_suffix_sum, 1);
            assert(min_suffix_sum(a@, b@, n as int, n as int) == 0int);
            assert(suffix[n as int] as int == 0);
            assert(suffix[n as int] as int == min_suffix_sum(a@, b@, n as int, n as int));
        }
        
        let mut i: usize = n;
        while i > 0
            invariant
                0 <= i <= n,
                n <= 200_000,
                n == a.len(),
                a.len() == b.len(),
                suffix.len() == n + 1,
                forall|j: int| 0 <= j < a.len() ==> 1 <= #[trigger] a[j] <= 1_000_000_000,
                forall|j: int| 0 <= j < b.len() ==> 1 <= #[trigger] b[j] <= 1_000_000_000,
                forall|j: int| (i as int) <= j <= (n as int) ==> #[trigger] suffix[j] as int == min_suffix_sum(a@, b@, j, n as int),
                forall|j: int| (i as int) <= j <= (n as int) ==> 0 <= #[trigger] suffix[j] <= (n as int - j) * 1_000_000_000,
                a@.len() == n,
                b@.len() == n,
            decreases i,
        {
            i = i - 1;
            proof {
                reveal_with_fuel(min_suffix_sum, 2);
                lemma_min_suffix_sum_bound(a@, b@, i as int, n as int);
                lemma_min_suffix_sum_bound(a@, b@, (i + 1) as int, n as int);
                assert(min_suffix_sum(a@, b@, i as int, n as int)
                    == min2(a@[i as int] as int, b@[i as int] as int)
                       + min_suffix_sum(a@, b@, (i + 1) as int, n as int));
                assert(suffix[(i + 1) as int] as int == min_suffix_sum(a@, b@, (i + 1) as int, n as int));
                assert(1 <= a@[i as int] <= 1_000_000_000);
                assert(1 <= b@[i as int] <= 1_000_000_000);
                assert(suffix[(i + 1) as int] <= (n as int - (i + 1) as int) * 1_000_000_000);
                assert((n as int - (i + 1) as int) * 1_000_000_000 + 1_000_000_000
                    == (n as int - (i as int)) * 1_000_000_000) by(nonlinear_arith);
            }
            let m_val: i64 = if a[i] < b[i] { a[i] } else { b[i] };
            suffix.set(i, suffix[i + 1] + m_val);
            proof {
                assert(suffix[i as int] as int == min_suffix_sum(a@, b@, i as int, n as int));
            }
        }
        
        proof {
            assert(suffix[1 as int] as int == min_suffix_sum(a@, b@, 1, n as int));
            assert(cost_at(a@, b@, 0) == a@[0] as int + min_suffix_sum(a@, b@, 1, n as int));
            lemma_min_suffix_sum_bound(a@, b@, 1, n as int);
            assert(suffix[1 as int] <= (n as int - 1) * 1_000_000_000);
            assert((n as int - 1) * 1_000_000_000 <= 200_000 * 1_000_000_000) by(nonlinear_arith) requires (n as int - 1) <= 200_000;
            assert(1 <= a@[0] <= 1_000_000_000);
        }
        let mut best: i64 = a[0] + suffix[1];
        proof {
            assert(best as int == cost_at(a@, b@, 0));
            reveal_with_fuel(min_cost, 2);
            assert(min_cost(a@, b@, 1) == cost_at(a@, b@, 0));
        }
        let mut j: usize = 1;
        while j < m
            invariant
                1 <= j <= m,
                m <= n,
                n <= 200_000,
                n == a.len(),
                a.len() == b.len(),
                a@.len() == n,
                b@.len() == n,
                suffix.len() == n + 1,
                forall|jj: int| 0 <= jj < a.len() ==> 1 <= #[trigger] a[jj] <= 1_000_000_000,
                forall|jj: int| 0 <= jj < b.len() ==> 1 <= #[trigger] b[jj] <= 1_000_000_000,
                forall|jj: int| 0 <= jj <= (n as int) ==> #[trigger] suffix[jj] as int == min_suffix_sum(a@, b@, jj, n as int),
                forall|jj: int| 0 <= jj <= (n as int) ==> 0 <= #[trigger] suffix[jj] <= (n as int - jj) * 1_000_000_000,
                best as int == min_cost(a@, b@, j as int),
            decreases m - j,
        {
            proof {
                lemma_min_suffix_sum_bound(a@, b@, (j + 1) as int, n as int);
                assert(suffix[(j + 1) as int] as int == min_suffix_sum(a@, b@, (j + 1) as int, n as int));
                assert(1 <= a@[j as int] <= 1_000_000_000);
                assert(suffix[(j + 1) as int] <= (n as int - (j + 1) as int) * 1_000_000_000);
                assert((n as int - (j + 1) as int) * 1_000_000_000 <= 200_000 * 1_000_000_000) by(nonlinear_arith) requires (n as int - (j + 1) as int) <= 200_000;
            }
            let cost: i64 = a[j] + suffix[j + 1];
            proof {
                assert(cost as int == cost_at(a@, b@, j as int));
                reveal_with_fuel(min_cost, 2);
                assert(min_cost(a@, b@, (j + 1) as int)
                    == if cost_at(a@, b@, j as int) < min_cost(a@, b@, j as int)
                       { cost_at(a@, b@, j as int) }
                       else { min_cost(a@, b@, j as int) });
            }
            if cost < best {
                best = cost;
            }
            j = j + 1;
        }
        best
    }
}

}
