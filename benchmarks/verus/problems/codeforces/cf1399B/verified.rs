use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn min_seq(a: Seq<u64>) -> u64
    recommends
        a.len() > 0,
    decreases a.len(),
{
    if a.len() <= 1 {
        a[0]
    } else {
        let m = min_seq(a.subrange(0, a.len() - 1));
        if a[a.len() - 1] < m {
            a[a.len() - 1]
        } else {
            m
        }
    }
}

pub open spec fn max_int(x: int, y: int) -> int {
    if x >= y { x } else { y }
}

pub open spec fn cost_sum(a: Seq<u64>, b: Seq<u64>, ma: u64, mb: u64) -> int
    recommends
        a.len() == b.len(),
    decreases a.len(),
{
    if a.len() == 0 {
        0
    } else {
        let last = a.len() - 1;
        let prev = cost_sum(a.subrange(0, last), b.subrange(0, last), ma, mb);
        prev + max_int(a[last] as int - ma as int, b[last] as int - mb as int)
    }
}

pub open spec fn min_prefix(a: Seq<u64>, k: int) -> u64
    recommends
        1 <= k <= a.len(),
    decreases k,
{
    if k <= 1 {
        a[0]
    } else {
        let m = min_prefix(a, k - 1);
        if a[k - 1] < m { a[k - 1] } else { m }
    }
}

pub open spec fn cost_prefix(a: Seq<u64>, b: Seq<u64>, ma: u64, mb: u64, k: int) -> int
    decreases k,
{
    if k <= 0 {
        0
    } else {
        let prev = cost_prefix(a, b, ma, mb, k - 1);
        prev + max_int(a[k - 1] as int - ma as int, b[k - 1] as int - mb as int)
    }
}

proof fn lemma_min_prefix_eq_min_seq(a: Seq<u64>, k: int)
    requires
        1 <= k <= a.len(),
    ensures
        min_prefix(a, k) == min_seq(a.subrange(0, k)),
    decreases k,
{
    if k <= 1 {
        assert(a.subrange(0, 1)[0] == a[0]);
    } else {
        lemma_min_prefix_eq_min_seq(a, k - 1);
        assert(a.subrange(0, k).subrange(0, k - 1) == a.subrange(0, k - 1));
        assert(a.subrange(0, k)[k - 1] == a[k - 1]);
    }
}

proof fn lemma_min_prefix_le(a: Seq<u64>, k: int, i: int)
    requires
        1 <= k <= a.len(),
        0 <= i < k,
    ensures
        min_prefix(a, k) <= a[i],
    decreases k,
{
    if k == 1 {
    } else {
        if i < k - 1 {
            lemma_min_prefix_le(a, k - 1, i);
        }
    }
}

proof fn lemma_cost_prefix_eq_cost_sum(a: Seq<u64>, b: Seq<u64>, ma: u64, mb: u64, k: int)
    requires
        a.len() == b.len(),
        0 <= k <= a.len(),
    ensures
        cost_prefix(a, b, ma, mb, k) == cost_sum(a.subrange(0, k), b.subrange(0, k), ma, mb),
    decreases k,
{
    if k <= 0 {
    } else {
        lemma_cost_prefix_eq_cost_sum(a, b, ma, mb, k - 1);
        assert(a.subrange(0, k).subrange(0, k - 1) == a.subrange(0, k - 1));
        assert(b.subrange(0, k).subrange(0, k - 1) == b.subrange(0, k - 1));
        assert(a.subrange(0, k)[k - 1] == a[k - 1]);
        assert(b.subrange(0, k)[k - 1] == b[k - 1]);
    }
}

impl Solution {
    pub fn min_moves_to_equalize(n: usize, a: Vec<u64>, b: Vec<u64>) -> (result: u64)
        requires
            1 <= n <= 50,
            a.len() == n,
            b.len() == n,
            forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= 1_000_000_000u64,
            forall|i: int| 0 <= i < b.len() ==> 1 <= #[trigger] b[i] <= 1_000_000_000u64,
        ensures
            result as int == cost_sum(a@, b@, min_seq(a@), min_seq(b@)),
    {
        let mut ma: u64 = a[0];
        let mut mb: u64 = b[0];
        let mut i: usize = 1;
        while i < n
            invariant
                1 <= i <= n,
                a.len() == n,
                b.len() == n,
                1 <= n <= 50,
                ma == min_prefix(a@, i as int),
                mb == min_prefix(b@, i as int),
                forall|j: int| 0 <= j < a.len() ==> 1 <= #[trigger] a[j] <= 1_000_000_000u64,
                forall|j: int| 0 <= j < b.len() ==> 1 <= #[trigger] b[j] <= 1_000_000_000u64,
            decreases n - i,
        {
            if a[i] < ma { ma = a[i]; }
            if b[i] < mb { mb = b[i]; }
            i += 1;
        }
        proof {
            lemma_min_prefix_eq_min_seq(a@, n as int);
            lemma_min_prefix_eq_min_seq(b@, n as int);
            assert(a@.subrange(0, n as int) == a@);
            assert(b@.subrange(0, n as int) == b@);
        }
        let ghost ma_g = ma;
        let ghost mb_g = mb;
        let mut total: u64 = 0;
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j <= n,
                a.len() == n,
                b.len() == n,
                1 <= n <= 50,
                ma == ma_g,
                mb == mb_g,
                ma == min_prefix(a@, n as int),
                mb == min_prefix(b@, n as int),
                forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= 1_000_000_000u64,
                forall|i: int| 0 <= i < b.len() ==> 1 <= #[trigger] b[i] <= 1_000_000_000u64,
                total as int == cost_prefix(a@, b@, ma, mb, j as int),
                total as int <= (j as int) * 1_000_000_000,
            decreases n - j,
        {
            proof {
                lemma_min_prefix_le(a@, n as int, j as int);
                lemma_min_prefix_le(b@, n as int, j as int);
            }
            let da = a[j] - ma;
            let db = b[j] - mb;
            let m = if da >= db { da } else { db };
            total = total + m;
            j += 1;
        }
        proof {
            lemma_cost_prefix_eq_cost_sum(a@, b@, ma, mb, n as int);
            assert(a@.subrange(0, n as int) == a@);
            assert(b@.subrange(0, n as int) == b@);
        }
        total
    }
}

}
