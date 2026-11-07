use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn table_value(n: int, i: int, j: int) -> int
    decreases i + j,
{
    if i < 0 || j < 0 || i >= n || j >= n {
        0int
    } else if i == 0 || j == 0 {
        1int
    } else {
        table_value(n, i - 1, j) + table_value(n, i, j - 1)
    }
}

pub open spec fn pow2(k: int) -> int
    decreases k,
{
    if k <= 0 { 1int } else { 2 * pow2(k - 1) }
}

proof fn lemma_pow2_pos(k: int)
    requires
        0 <= k,
    ensures
        pow2(k) >= 1,
    decreases k,
{
    if k > 0 {
        lemma_pow2_pos(k - 1);
    }
}


proof fn lemma_pow2_monotonic(k: int, m: int)
    requires
        0 <= k <= m,
    ensures
        pow2(k) <= pow2(m),
    decreases m - k,
{
    lemma_pow2_pos(k);
    lemma_pow2_pos(m);
    if k < m {
        lemma_pow2_monotonic(k, m - 1);
        assert(pow2(m) == 2 * pow2(m - 1));
    }
}

proof fn lemma_pow2_19()
    ensures
        pow2(19) == 524288,
{
    reveal_with_fuel(pow2, 21);
}

proof fn lemma_pow2_bound(k: int)
    requires
        0 <= k <= 19,
    ensures
        pow2(k) <= 524288,
        pow2(k) >= 1,
{
    lemma_pow2_19();
    lemma_pow2_monotonic(k, 19);
    lemma_pow2_pos(k);
}

proof fn lemma_table_bound(n: int, i: int, j: int)
    requires
        1 <= n <= 10,
        0 <= i < n,
        0 <= j < n,
    ensures
        1 <= table_value(n, i, j) <= pow2(i + j + 1),
    decreases i + j,
{
    if i == 0 || j == 0 {
        assert(table_value(n, i, j) == 1);
        assert(pow2(i + j + 1) >= 1) by {
            lemma_pow2_bound(i + j + 1);
        }
    } else {
        lemma_table_bound(n, i - 1, j);
        lemma_table_bound(n, i, j - 1);
        assert(pow2(i + j + 1) == 2 * pow2(i + j));
        assert(table_value(n, i - 1, j) <= pow2((i - 1) + j + 1));
        assert((i - 1) + j + 1 == i + j);
        assert(table_value(n, i, j - 1) <= pow2(i + (j - 1) + 1));
        assert(i + (j - 1) + 1 == i + j);
    }
}

impl Solution {
    pub fn max_in_table(n: u32) -> (result: u32)
        requires
            1 <= n <= 10,
        ensures
            result as int == table_value(n as int, (n - 1) as int, (n - 1) as int),
    {
        let nu: usize = n as usize;
        let mut row: Vec<u32> = Vec::new();
        let mut k: usize = 0;
        while k < nu
            invariant
                k <= nu,
                nu == n as usize,
                1 <= n <= 10,
                row.len() == k,
                forall|t: int| 0 <= t < k ==> row[t] == 1u32,
            decreases nu - k,
        {
            row.push(1u32);
            k = k + 1;
        }
        proof {
            assert forall|t: int| 0 <= t < n as int implies row[t] as int == table_value(n as int, 0, t) by {
                assert(row[t] == 1u32);
            };
        }
        let mut i: usize = 1;
        while i < nu
            invariant
                1 <= i <= nu,
                nu == n as usize,
                1 <= n <= 10,
                row.len() == nu,
                forall|t: int| 0 <= t < nu as int ==> #[trigger] row[t] as int == table_value(n as int, (i - 1) as int, t),
                forall|t: int| 0 <= t < nu as int ==> 1 <= #[trigger] row[t] as int <= 524288,
            decreases nu - i,
        {
            let mut j: usize = 1;
            while j < nu
                invariant
                    1 <= j <= nu,
                    1 <= i < nu,
                    nu == n as usize,
                    1 <= n <= 10,
                    row.len() == nu,
                    forall|t: int| 0 <= t < j as int ==> #[trigger] row[t] as int == table_value(n as int, i as int, t),
                    forall|t: int| j as int <= t < nu as int ==> #[trigger] row[t] as int == table_value(n as int, (i - 1) as int, t),
                    forall|t: int| 0 <= t < nu as int ==> 1 <= #[trigger] row[t] as int <= 524288,
                decreases nu - j,
            {
                proof {
                    assert(row[j as int] as int == table_value(n as int, (i - 1) as int, j as int));
                    assert(row[(j - 1) as int] as int == table_value(n as int, i as int, (j - 1) as int));
                    assert(table_value(n as int, i as int, j as int) ==
                           table_value(n as int, (i - 1) as int, j as int) +
                           table_value(n as int, i as int, (j - 1) as int));
                    lemma_table_bound(n as int, i as int, j as int);
                    lemma_pow2_bound(i as int + j as int + 1);
                }
                let v: u32 = row[j] + row[j - 1];
                row.set(j, v);
                j = j + 1;
            }
            i = i + 1;
        }
        proof {
            assert(i == nu);
            assert(row[(nu - 1) as int] as int == table_value(n as int, (i - 1) as int, (nu - 1) as int));
        }
        row[nu - 1]
    }
}

}
