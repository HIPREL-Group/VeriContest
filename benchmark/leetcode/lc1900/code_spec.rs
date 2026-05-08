use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_min(a: int, b: int) -> int {
    if a <= b { a } else { b }
}

pub open spec fn spec_max(a: int, b: int) -> int {
    if a >= b { a } else { b }
}

pub open spec fn scan_j_early(l: int, r: int, m: int, i: int, j: int, j_hi: int) -> int
    decreases m, 0int, spec_max(j_hi - j + 1, 0)
{
    if j > j_hi || j < 1 || m < 3 {
        30
    } else {
        let nxt = (m + 1) / 2;
        let ii = spec_min(i, j);
        let jj = spec_max(i, j);
        let cur = 1 + spec_earliest(ii, jj, nxt);
        let rest = scan_j_early(l, r, m, i, j + 1, j_hi);
        spec_min(cur, rest)
    }
}

pub open spec fn scan_i_early(l: int, r: int, m: int, i: int) -> int
    decreases m, 1int, spec_max(l - i + 1, 0)
{
    if i > l || i < 1 || m < 3 {
        30
    } else {
        let nxt = (m + 1) / 2;
        let j_lo = spec_max(l - i + 1, spec_max(l + r - m / 2 - i, 1));
        let j_hi = spec_min(r - i, nxt - i);
        let cur = scan_j_early(l, r, m, i, j_lo, j_hi);
        let rest = scan_i_early(l, r, m, i + 1);
        spec_min(cur, rest)
    }
}

pub open spec fn spec_earliest(l: int, r: int, m: int) -> int
    decreases m, 2int, 0int
{
    let ll = spec_min(l, r);
    let rr = spec_max(l, r);
    if m < 2 || ll < 1 || rr < 1 || ll + rr > m {
        30
    } else if ll == rr {
        1
    } else {
        scan_i_early(ll, rr, m, 1)
    }
}

pub open spec fn scan_j_late(l: int, r: int, m: int, i: int, j: int, j_hi: int) -> int
    decreases m, 0int, spec_max(j_hi - j + 1, 0)
{
    if j > j_hi || j < 1 || m < 3 {
        0
    } else {
        let nxt = (m + 1) / 2;
        let ii = spec_min(i, j);
        let jj = spec_max(i, j);
        let cur = 1 + spec_latest(ii, jj, nxt);
        let rest = scan_j_late(l, r, m, i, j + 1, j_hi);
        spec_max(cur, rest)
    }
}

pub open spec fn scan_i_late(l: int, r: int, m: int, i: int) -> int
    decreases m, 1int, spec_max(l - i + 1, 0)
{
    if i > l || i < 1 || m < 3 {
        0
    } else {
        let nxt = (m + 1) / 2;
        let j_lo = spec_max(l - i + 1, spec_max(l + r - m / 2 - i, 1));
        let j_hi = spec_min(r - i, nxt - i);
        let cur = scan_j_late(l, r, m, i, j_lo, j_hi);
        let rest = scan_i_late(l, r, m, i + 1);
        spec_max(cur, rest)
    }
}

pub open spec fn spec_latest(l: int, r: int, m: int) -> int
    decreases m, 2int, 0int
{
    let ll = spec_min(l, r);
    let rr = spec_max(l, r);
    if m < 2 || ll < 1 || rr < 1 || ll + rr > m {
        0
    } else if ll == rr {
        1
    } else {
        scan_i_late(ll, rr, m, 1)
    }
}

impl Solution {
    fn dp(l: i32, r: i32, m: i32) -> (result: (i32, i32))
        requires
            1 <= l <= r,
            l + r <= m,
            2 <= m <= 28,
        ensures
            result.0 as int == spec_earliest(l as int, r as int, m as int),
            result.1 as int == spec_latest(l as int, r as int, m as int),
        decreases m,
    {
        if l == r {
            return (1, 1);
        }
        let nxt = (m + 1) / 2;
        let mut best_min = 30i32;
        let mut best_max = 0i32;
        let mut i = 1i32;
        while i <= l {
            let j_lo_a = l - i + 1;
            let j_lo_b = l + r - m / 2 - i;
            let mut j_lo = if j_lo_a >= j_lo_b { j_lo_a } else { j_lo_b };
            if j_lo < 1 {
                j_lo = 1;
            }
            let j_hi_a = r - i;
            let j_hi_b = nxt - i;
            let j_hi = if j_hi_a <= j_hi_b { j_hi_a } else { j_hi_b };
            let mut local_min = 30i32;
            let mut local_max = 0i32;
            let mut j = j_lo;
            while j <= j_hi {
                let ii = if i <= j { i } else { j };
                let jj = if i <= j { j } else { i };
                let (sub_min, sub_max) = Self::dp(ii, jj, nxt);
                if sub_min + 1 < local_min {
                    local_min = sub_min + 1;
                }
                if sub_max + 1 > local_max {
                    local_max = sub_max + 1;
                }
                j += 1;
            }
            if local_min < best_min {
                best_min = local_min;
            }
            if local_max > best_max {
                best_max = local_max;
            }
            i += 1;
        }
        (best_min, best_max)
    }

    pub fn earliest_and_latest(n: i32, first_player: i32, second_player: i32) -> (result: Vec<i32>)
        requires
            2 <= n <= 28,
            1 <= first_player < second_player <= n,
        ensures
            result@.len() == 2,
            result@[0] == spec_earliest(first_player as int, (n - second_player + 1) as int, n as int),
            result@[1] == spec_latest(first_player as int, (n - second_player + 1) as int, n as int),
    {
        let l0 = first_player;
        let r0 = n - second_player + 1;
        let ll = if l0 <= r0 { l0 } else { r0 };
        let rr = if l0 <= r0 { r0 } else { l0 };
        let (e, la) = Self::dp(ll, rr, n);
        vec![e, la]
    }
}

} 
