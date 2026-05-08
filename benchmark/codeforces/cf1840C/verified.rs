use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn subarray_all_leq(a: Seq<i64>, q: i64, l: int, r: int) -> bool {
    forall|i: int| l <= i && i <= r ==> #[trigger] a[i] <= q
}

pub open spec fn valid_interval(n: int, k: int, q: i64, a: Seq<i64>, l: int, r: int) -> bool {
    0 <= l && l <= r && r < n && r - l + 1 >= k && subarray_all_leq(a, q, l, r)
}

pub open spec fn pair_contrib(n: int, k: int, q: i64, a: Seq<i64>, l: int, r: int) -> int {
    if valid_interval(n, k, q, a, l, r) {
        1
    } else {
        0
    }
}

pub open spec fn sum_r(n: int, k: int, q: i64, a: Seq<i64>, l: int, r: int) -> int
    decreases n - r
{
    if r >= n {
        0
    } else {
        pair_contrib(n, k, q, a, l, r) + sum_r(n, k, q, a, l, r + 1)
    }
}

pub open spec fn sum_l(n: int, k: int, q: i64, a: Seq<i64>, l: int) -> int
    decreases n - l
{
    if l >= n {
        0
    } else {
        sum_r(n, k, q, a, l, l) + sum_l(n, k, q, a, l + 1)
    }
}

pub open spec fn vacation_count(n: int, k: int, q: i64, a: Seq<i64>) -> int {
    if n <= 0 {
        0
    } else {
        sum_l(n, k, q, a, 0)
    }
}

pub open spec fn extend_good_end(q: i64, a: Seq<i64>, pos: int) -> int
    recommends
        0 <= pos <= a.len(),
    decreases a.len() as int - pos
{
    let n = a.len() as int;
    if pos >= n {
        n
    } else if a[pos] > q {
        pos
    } else {
        proof {
            assert(pos < n);
            assert(n - (pos + 1) < n - pos);
        }
        extend_good_end(q, a, pos + 1)
    }
}

pub open spec fn triangle_contrib(L: int, k: int) -> int {
    if L >= k {
        (L - k + 1) * (L - k + 2) / 2
    } else {
        0
    }
}

pub proof fn lemma_extend_good_end_gt_pos(q: i64, a: Seq<i64>, pos: int)
    requires
        0 <= pos < a.len(),
        a[pos] <= q,
    ensures
        extend_good_end(q, a, pos) > pos,
    decreases a.len() as int - pos,
{
    let n = a.len() as int;
    reveal_with_fuel(extend_good_end, 10);
    if pos + 1 >= n {
        assert(pos == n - 1);
        assert(extend_good_end(q, a, pos) == n);
        assert(n > pos);
    } else if a[pos + 1] > q {
        assert(extend_good_end(q, a, pos) == pos + 1);
        assert(pos + 1 > pos);
    } else {
        assert(a[pos + 1] <= q);
        assert(0 <= pos + 1 < n);
        lemma_extend_good_end_gt_pos(q, a, pos + 1);
    }
}

pub proof fn lemma_extend_good_end_le_len(q: i64, a: Seq<i64>, pos: int)
    requires
        0 <= pos <= a.len(),
    ensures
        pos <= extend_good_end(q, a, pos) && extend_good_end(q, a, pos) <= a.len() as int,
    decreases a.len() as int - pos,
{
    let n = a.len() as int;
    reveal_with_fuel(extend_good_end, 10);
    if pos >= n {
        assert(extend_good_end(q, a, pos) == n);
    } else if a[pos] > q {
        assert(extend_good_end(q, a, pos) == pos);
        assert(pos <= n);
    } else {
        lemma_extend_good_end_le_len(q, a, pos + 1);
    }
}

pub open spec fn scan_total(k: int, q: i64, a: Seq<i64>, pos: int) -> int
    recommends
        0 <= pos <= a.len(),
    decreases a.len() as int - pos
        when 0 <= pos && pos <= a.len() as int
{
    let n = a.len() as int;
    if pos >= n {
        0
    } else if a[pos] > q {
        proof {
            assert(pos < n);
            assert(n - (pos + 1) < n - pos);
        }
        scan_total(k, q, a, pos + 1)
    } else {
        proof {
            assert(pos < n);
            assert(pos < a.len());
            assert(!(a[pos] > q));
            assert(a[pos] <= q);
            lemma_extend_good_end_gt_pos(q, a, pos);
            lemma_extend_good_end_le_len(q, a, pos);
        }
        let end = extend_good_end(q, a, pos);
        proof {
            assert(end > pos);
            assert(end <= n);
            assert(n - end < n - pos);
        }
        triangle_contrib(end - pos, k) + scan_total(k, q, a, end)
    }
}

pub proof fn lemma_scan_total_nonneg(k: int, q: i64, a: Seq<i64>, pos: int)
    requires
        0 <= pos <= a.len(),
    ensures
        scan_total(k, q, a, pos) >= 0,
    decreases a.len() as int - pos,
{
    let n = a.len() as int;
    reveal_with_fuel(scan_total, 2);
    if pos >= n {
    } else if a[pos] > q {
        lemma_scan_total_nonneg(k, q, a, pos + 1);
    } else {
        lemma_extend_good_end_gt_pos(q, a, pos);
        lemma_extend_good_end_le_len(q, a, pos);
        let end = extend_good_end(q, a, pos);
        lemma_scan_total_nonneg(k, q, a, end);
    }
}

pub proof fn lemma_scan_total_bound(k: int, q: i64, a: Seq<i64>, pos: int)
    requires
        0 <= pos <= a.len(),
        k >= 1,
    ensures
        scan_total(k, q, a, pos) <= (a.len() as int - pos) * (a.len() as int - pos + 1) / 2,
    decreases a.len() as int - pos,
{
    let n = a.len() as int;
    reveal_with_fuel(scan_total, 2);
    if pos >= n {
    } else if a[pos] > q {
        lemma_scan_total_bound(k, q, a, pos + 1);
        assert((n - (pos + 1)) * (n - (pos + 1) + 1) / 2 <= (n - pos) * (n - pos + 1) / 2) by (nonlinear_arith)
            requires n - pos >= 1;
    } else {
        lemma_extend_good_end_gt_pos(q, a, pos);
        lemma_extend_good_end_le_len(q, a, pos);
        let end = extend_good_end(q, a, pos);
        let seg = end - pos;
        lemma_scan_total_bound(k, q, a, end);
        assert(triangle_contrib(seg, k) <= seg * (seg + 1) / 2) by {
            if seg >= k {
                assert((seg - k + 1) * (seg - k + 2) / 2 <= seg * (seg + 1) / 2) by (nonlinear_arith)
                    requires seg >= k, k >= 1;
            }
        }
        assert(seg * (seg + 1) / 2 + (n - end) * (n - end + 1) / 2 <= (n - pos) * (n - pos + 1) / 2) by (nonlinear_arith)
            requires seg == end - pos, end > pos, end <= n, seg >= 1;
    }
}

pub struct Solution;

impl Solution {
    pub fn count_vacations(n: usize, k: usize, q: i64, a: Vec<i64>) -> (res: i64)
        requires
            1 <= n && n <= 200000,
            1 <= k && k <= n,
            a.len() == n,
            forall|i: int| 0 <= i && i < n ==> -1000000000 <= a@[i] && a@[i] <= 1000000000,
        ensures
            res as int == scan_total(k as int, q, a@, 0),
    {
        proof {
            lemma_scan_total_nonneg(k as int, q, a@, 0);
            lemma_scan_total_bound(k as int, q, a@, 0);
        }
        let mut pos: usize = 0;
        let mut total: i64 = 0;
        #[verifier::loop_isolation(false)]
        while pos < n
            invariant
                0 <= pos <= n,
                n == a.len(),
                n <= 200000,
                1 <= k <= n,
                total as int + scan_total(k as int, q, a@, pos as int) == scan_total(k as int, q, a@, 0),
                0 <= total,
                scan_total(k as int, q, a@, 0) <= (n as int) * (n as int + 1) / 2,
                forall|i: int| 0 <= i && i < n ==> -1000000000 <= a@[i] && a@[i] <= 1000000000,
            decreases n - pos,
        {
            if a[pos] > q {
                proof {
                    assert(pos < n);
                    assert((a@)[pos as int] > q);
                    reveal_with_fuel(scan_total, 2);
                    assert(scan_total(k as int, q, a@, pos as int) == scan_total(k as int, q, a@, (pos + 1) as int));
                }
                pos += 1;
            } else {
                let start = pos;
                proof {
                    assert((a@)[start as int] <= q);
                    assert(start < n);
                    lemma_extend_good_end_le_len(q, a@, start as int);
                }
                #[verifier::loop_isolation(false)]
                while pos < n && a[pos] <= q
                    invariant
                        start <= pos <= n,
                        n == a.len(),
                        n <= 200000,
                        1 <= k <= n,
                        forall|j: int|
                            start as int <= j && j < pos as int ==> (a@)[j] <= q,
                        extend_good_end(q, a@, start as int) == extend_good_end(q, a@, pos as int),
                        total as int + scan_total(k as int, q, a@, start as int) == scan_total(k as int, q, a@, 0),
                        0 <= total,
                        scan_total(k as int, q, a@, 0) <= (n as int) * (n as int + 1) / 2,
                        forall|i: int| 0 <= i && i < n ==> -1000000000 <= a@[i] && a@[i] <= 1000000000,
                    decreases n - pos,
                {
                    proof {
                        assert(pos < n);
                        assert((a@)[pos as int] <= q);
                        reveal_with_fuel(extend_good_end, 2);
                        assert(extend_good_end(q, a@, pos as int) == extend_good_end(q, a@, (pos + 1) as int));
                    }
                    pos += 1;
                }
                let seg_len = pos - start;
                proof {
                    reveal_with_fuel(extend_good_end, 2);
                    assert(extend_good_end(q, a@, pos as int) == pos as int);
                    assert(extend_good_end(q, a@, start as int) == pos as int);
                    reveal_with_fuel(scan_total, 2);
                    lemma_extend_good_end_gt_pos(q, a@, start as int);
                    lemma_extend_good_end_le_len(q, a@, start as int);
                    assert(
                        scan_total(k as int, q, a@, start as int)
                            == triangle_contrib(pos as int - start as int, k as int)
                                + scan_total(k as int, q, a@, pos as int)
                    );
                    lemma_scan_total_nonneg(k as int, q, a@, pos as int);
                }
                if seg_len >= k {
                    proof {
                        assert(seg_len as int <= n as int);
                        assert(seg_len as int >= k as int);
                        assert(total as int + triangle_contrib(pos as int - start as int, k as int)
                            + scan_total(k as int, q, a@, pos as int)
                            == scan_total(k as int, q, a@, 0));
                        assert(scan_total(k as int, q, a@, pos as int) >= 0);
                        assert(total as int + triangle_contrib(pos as int - start as int, k as int)
                            <= scan_total(k as int, q, a@, 0));
                        assert(scan_total(k as int, q, a@, 0) <= (n as int) * (n as int + 1) / 2);
                        assert((n as int) * (n as int + 1) / 2 <= 200000int * 200001 / 2) by (nonlinear_arith)
                            requires n as int <= 200000;
                    }
                    let x = (seg_len - k) as i64 + 1;
                    proof {
                        assert(x as int == seg_len as int - k as int + 1);
                        assert(1 <= x as int <= n as int);
                        assert(x as int <= 200000);
                        assert(x as int * (x as int + 1) <= 200000int * 200001) by (nonlinear_arith)
                            requires 1 <= x as int, x as int <= 200000;
                        assert(200000int * 200001 < 9223372036854775807int);
                        assert(triangle_contrib(seg_len as int, k as int) == x as int * (x as int + 1) / 2);
                        assert(total as int + x as int * (x as int + 1) / 2
                            <= scan_total(k as int, q, a@, 0));
                        assert(total as int + x as int * (x as int + 1) / 2
                            <= 200000int * 200001 / 2);
                        assert(200000int * 200001 / 2 < 9223372036854775807int);
                    }
                    total += x * (x + 1) / 2;
                }
                proof {
                    assert(
                        total as int + scan_total(k as int, q, a@, pos as int)
                            == scan_total(k as int, q, a@, 0)
                    );
                }
            }
        }
        proof {
            assert(pos == n);
            reveal_with_fuel(scan_total, 2);
            assert(scan_total(k as int, q, a@, pos as int) == 0);
            assert(total as int == scan_total(k as int, q, a@, 0));
        }
        total
    }
}

}
