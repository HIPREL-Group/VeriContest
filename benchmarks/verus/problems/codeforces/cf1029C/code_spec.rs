use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn max_l_prefix(l: Seq<i64>, len: int) -> int
    decreases len,
{
    if len <= 0 {
        0int
    } else if len == 1 {
        l[0] as int
    } else {
        let m = max_l_prefix(l, len - 1);
        let v = l[len - 1] as int;
        if v > m {
            v
        } else {
            m
        }
    }
}

pub open spec fn max_l_suffix(l: Seq<i64>, j: int, n: int) -> int
    decreases n - j,
{
    if j >= n {
        0int
    } else if j + 1 == n {
        l[j] as int
    } else {
        let m = max_l_suffix(l, j + 1, n);
        let v = l[j] as int;
        if v > m {
            v
        } else {
            m
        }
    }
}

pub open spec fn min_r_prefix(r: Seq<i64>, len: int) -> int
    decreases len,
{
    if len <= 0 {
        0int
    } else if len == 1 {
        r[0] as int
    } else {
        let m = min_r_prefix(r, len - 1);
        let v = r[len - 1] as int;
        if v < m {
            v
        } else {
            m
        }
    }
}

pub open spec fn min_r_suffix(r: Seq<i64>, j: int, n: int) -> int
    decreases n - j,
{
    if j >= n {
        0int
    } else if j + 1 == n {
        r[j] as int
    } else {
        let m = min_r_suffix(r, j + 1, n);
        let v = r[j] as int;
        if v < m {
            v
        } else {
            m
        }
    }
}

pub open spec fn max_l_excluding(l: Seq<i64>, n: int, k: int) -> int {
    if k == 0 {
        max_l_suffix(l, 1, n)
    } else if k == n - 1 {
        max_l_prefix(l, n - 1)
    } else {
        let a = max_l_prefix(l, k);
        let b = max_l_suffix(l, k + 1, n);
        if a > b {
            a
        } else {
            b
        }
    }
}

pub open spec fn min_r_excluding(r: Seq<i64>, n: int, k: int) -> int {
    if k == 0 {
        min_r_suffix(r, 1, n)
    } else if k == n - 1 {
        min_r_prefix(r, n - 1)
    } else {
        let a = min_r_prefix(r, k);
        let b = min_r_suffix(r, k + 1, n);
        if a < b {
            a
        } else {
            b
        }
    }
}

pub open spec fn intersection_len_excluding(l: Seq<i64>, r: Seq<i64>, n: int, k: int) -> int {
    let ml = max_l_excluding(l, n, k);
    let mr = min_r_excluding(r, n, k);
    if ml > mr {
        0int
    } else {
        mr - ml
    }
}

impl Solution {
    pub fn maximal_intersection_len(l: Vec<i64>, r: Vec<i64>) -> (result: i64)
        requires
            2 <= l.len() <= 300_000,
            l.len() == r.len(),
            forall|i: int|
                0 <= i < l.len() ==> 0 <= #[trigger] l[i] && l[i] <= r[i] && r[i] <= 1_000_000_000,
        ensures
            result >= 0,
            forall|k: int|
                0 <= k < l.len() ==> intersection_len_excluding(l@, r@, l.len() as int, k) <= result as int,
            exists|k: int|
                0 <= k < l.len() && intersection_len_excluding(l@, r@, l.len() as int, k) == result as int,
    {
        let n = l.len();
        let mut pre_l: Vec<i64> = Vec::new();
        let mut i = 0usize;
        while i < n {
            if i == 0 {
                pre_l.push(l[i]);
            } else {
                let pl = pre_l[i - 1];
                let li = l[i];
                let m = if li > pl { li } else { pl };
                pre_l.push(m);
            }
            i = i + 1;
        }
        let mut suf_l: Vec<i64> = Vec::new();
        let mut z = 0usize;
        while z < n {
            suf_l.push(0i64);
            z = z + 1;
        }
        let mut i2 = n;
        while i2 > 0 {
            i2 = i2 - 1;
            let idx = i2;
            if idx + 1 == n {
                suf_l.set(idx, l[idx]);
            } else {
                let sl = suf_l[idx + 1];
                let li = l[idx];
                suf_l.set(idx, if li > sl { li } else { sl });
            }
        }
        let mut pre_r: Vec<i64> = Vec::new();
        let mut j = 0usize;
        while j < n {
            if j == 0 {
                pre_r.push(r[j]);
            } else {
                let pr = pre_r[j - 1];
                let rj = r[j];
                let m = if rj < pr { rj } else { pr };
                pre_r.push(m);
            }
            j = j + 1;
        }
        let mut suf_r: Vec<i64> = Vec::new();
        let mut w = 0usize;
        while w < n {
            suf_r.push(0i64);
            w = w + 1;
        }
        let mut i3 = n;
        while i3 > 0 {
            i3 = i3 - 1;
            let idx = i3;
            if idx + 1 == n {
                suf_r.set(idx, r[idx]);
            } else {
                let sr = suf_r[idx + 1];
                let rj = r[idx];
                suf_r.set(idx, if rj < sr { rj } else { sr });
            }
        }
        let mut ans = 0i64;
        let mut k = 0usize;
        while k < n {
            let ml = if k == 0 {
                suf_l[1]
            } else if k + 1 == n {
                pre_l[k - 1]
            } else {
                let a = pre_l[k - 1];
                let b = suf_l[k + 1];
                if a > b {
                    a
                } else {
                    b
                }
            };
            let mr = if k == 0 {
                suf_r[1]
            } else if k + 1 == n {
                pre_r[k - 1]
            } else {
                let a = pre_r[k - 1];
                let b = suf_r[k + 1];
                if a < b {
                    a
                } else {
                    b
                }
            };
            let cand = if ml > mr {
                0i64
            } else {
                mr.checked_sub(ml).unwrap()
            };
            if k == 0 {
                ans = cand;
            } else if cand > ans {
                ans = cand;
            }
            k = k + 1;
        }
        ans
    }
}

}
