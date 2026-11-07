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

proof fn lemma_scan_j_early_bound(l: int, r: int, m: int, i: int, j: int, j_hi: int)
    ensures
        scan_j_early(l, r, m, i, j, j_hi) <= 30,
    decreases m, 0int, spec_max(j_hi - j + 1, 0),
{
    reveal_with_fuel(scan_j_early, 2);
    if j > j_hi || j < 1 || m < 3 {
    } else {
        lemma_scan_j_early_bound(l, r, m, i, j + 1, j_hi);
    }
}

proof fn lemma_scan_i_early_bound(l: int, r: int, m: int, i: int)
    ensures
        scan_i_early(l, r, m, i) <= 30,
    decreases m, 1int, spec_max(l - i + 1, 0),
{
    reveal_with_fuel(scan_i_early, 2);
    if i > l || i < 1 || m < 3 {
    } else {
        lemma_scan_i_early_bound(l, r, m, i + 1);
    }
}

proof fn lemma_scan_j_late_bound(l: int, r: int, m: int, i: int, j: int, j_hi: int)
    ensures
        scan_j_late(l, r, m, i, j, j_hi) >= 0,
    decreases m, 0int, spec_max(j_hi - j + 1, 0),
{
    reveal_with_fuel(scan_j_late, 2);
    if j > j_hi || j < 1 || m < 3 {
    } else {
        lemma_scan_j_late_bound(l, r, m, i, j + 1, j_hi);
    }
}

proof fn lemma_scan_i_late_bound(l: int, r: int, m: int, i: int)
    ensures
        scan_i_late(l, r, m, i) >= 0,
    decreases m, 1int, spec_max(l - i + 1, 0),
{
    reveal_with_fuel(scan_i_late, 2);
    if i > l || i < 1 || m < 3 {
    } else {
        lemma_scan_i_late_bound(l, r, m, i + 1);
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
            0 <= result.0 <= 30,
            0 <= result.1 <= m,
        decreases m,
    {
        proof {
            reveal_with_fuel(spec_earliest, 2);
            reveal_with_fuel(spec_latest, 2);
        }
        if l == r {
            return (1, 1);
        }
        let nxt = (m + 1) / 2;
        let mut best_min = 30i32;
        let mut best_max = 0i32;
        let mut i = 1i32;

        proof {
            lemma_scan_i_early_bound(l as int, r as int, m as int, 1);
            lemma_scan_i_late_bound(l as int, r as int, m as int, 1);
        }

        while i <= l
            invariant
                1 <= l <= r,
                l < r,
                l + r <= m,
                3 <= m <= 28,
                nxt == (m + 1) / 2,
                1 <= i <= l + 1,
                0 <= best_max <= m,
                0 <= best_min <= 30,
                spec_min(best_min as int, scan_i_early(l as int, r as int, m as int, i as int))
                    == scan_i_early(l as int, r as int, m as int, 1),
                spec_max(best_max as int, scan_i_late(l as int, r as int, m as int, i as int))
                    == scan_i_late(l as int, r as int, m as int, 1),
            decreases l - i + 1,
        {
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

            proof {
                lemma_scan_j_early_bound(l as int, r as int, m as int, i as int, j_lo as int, j_hi as int);
                lemma_scan_j_late_bound(l as int, r as int, m as int, i as int, j_lo as int, j_hi as int);
            }

            while j <= j_hi
                invariant
                    1 <= l <= r,
                    l < r,
                    l + r <= m,
                    3 <= m <= 28,
                    nxt == (m + 1) / 2,
                    1 <= i <= l,
                    j_lo <= j <= j_hi + 1,
                    j_lo as int == spec_max((l - i + 1) as int, spec_max((l + r - m / 2 - i) as int, 1)),
                    j_hi as int == spec_min((r - i) as int, (nxt - i) as int),
                    0 <= local_max <= m,
                    0 <= local_min <= 30,
                    spec_min(local_min as int, scan_j_early(l as int, r as int, m as int, i as int, j as int, j_hi as int))
                        == scan_j_early(l as int, r as int, m as int, i as int, j_lo as int, j_hi as int),
                    spec_max(local_max as int, scan_j_late(l as int, r as int, m as int, i as int, j as int, j_hi as int))
                        == scan_j_late(l as int, r as int, m as int, i as int, j_lo as int, j_hi as int),
                decreases j_hi - j + 1,
            {
                let ii = if i <= j { i } else { j };
                let jj = if i <= j { j } else { i };

                proof {
                    assert(1 <= ii <= jj);
                    assert(ii + jj == i + j);
                    assert(j <= nxt - i) by {
                        assert(j <= j_hi);
                        assert(j_hi as int <= (nxt - i) as int);
                    }
                    assert(ii + jj <= nxt);
                    assert(m >= 3) by {
                        assert(l >= 1 && r >= 2 && l + r <= m);
                    }
                    assert(2 <= nxt <= 14) by {
                        assert(nxt == (m + 1) / 2);
                        assert(3 <= m <= 28);
                    }
                }

                let (sub_min, sub_max) = Self::dp(ii, jj, nxt);

                proof {
                    reveal_with_fuel(scan_j_early, 2);
                    reveal_with_fuel(scan_j_late, 2);
                    assert(sub_min as int == spec_earliest(ii as int, jj as int, nxt as int));
                    assert(sub_max as int == spec_latest(ii as int, jj as int, nxt as int));
                    assert(0 <= sub_min <= 30);
                    assert(0 <= sub_max <= nxt);
                    assert(sub_max + 1 <= nxt + 1 <= m) by {
                        assert(nxt == (m + 1) / 2);
                        assert(m >= 3);
                    }
                    lemma_scan_j_early_bound(l as int, r as int, m as int, i as int, (j + 1) as int, j_hi as int);
                    lemma_scan_j_late_bound(l as int, r as int, m as int, i as int, (j + 1) as int, j_hi as int);
                }

                if sub_min + 1 < local_min {
                    local_min = sub_min + 1;
                }
                if sub_max + 1 > local_max {
                    local_max = sub_max + 1;
                }
                j += 1;
            }

            proof {
                reveal_with_fuel(scan_j_early, 2);
                reveal_with_fuel(scan_j_late, 2);
                assert(local_min as int == scan_j_early(l as int, r as int, m as int, i as int, j_lo as int, j_hi as int));
                assert(local_max as int == scan_j_late(l as int, r as int, m as int, i as int, j_lo as int, j_hi as int));
                reveal_with_fuel(scan_i_early, 2);
                reveal_with_fuel(scan_i_late, 2);
                lemma_scan_i_early_bound(l as int, r as int, m as int, (i + 1) as int);
                lemma_scan_i_late_bound(l as int, r as int, m as int, (i + 1) as int);
            }

            if local_min < best_min {
                best_min = local_min;
            }
            if local_max > best_max {
                best_max = local_max;
            }

            i += 1;
        }

        proof {
            reveal_with_fuel(scan_i_early, 2);
            reveal_with_fuel(scan_i_late, 2);
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

        proof {
            reveal_with_fuel(spec_earliest, 2);
            reveal_with_fuel(spec_latest, 2);
        }

        let (e, la) = Self::dp(ll, rr, n);
        vec![e, la]
    }
}

} 
