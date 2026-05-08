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

pub open spec fn scan_total(k: int, q: i64, a: Seq<i64>, pos: int) -> int
    recommends
        0 <= pos <= a.len(),
    decreases a.len() as int - pos
{
    let n = a.len() as int;
    if pos >= n {
        0
    } else if a[pos] > q {
        scan_total(k, q, a, pos + 1)
    } else {
        let end = extend_good_end(q, a, pos);
        triangle_contrib(end - pos, k) + scan_total(k, q, a, end)
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
        let mut pos: usize = 0;
        let mut total: i64 = 0;
        while pos < n {
            if a[pos] > q {
                pos += 1;
            } else {
                let start = pos;
                while pos < n && a[pos] <= q {
                    pos += 1;
                }
                let seg_len = pos - start;
                if seg_len >= k {
                    let x = (seg_len - k) as i64 + 1;
                    total += x * (x + 1) / 2;
                }
            }
        }
        total
    }
}

}
