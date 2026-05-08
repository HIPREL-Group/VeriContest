use vstd::prelude::*;
use vstd::arithmetic::div_mod::{lemma_fundamental_div_mod, lemma_mod_multiples_vanish};

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    
    
    
    
    
    
    
    pub open spec fn dp_val(i: int, j: int, rm: Seq<i32>) -> int
        recommends 0 <= j < 6, rm.len() == 6,
        decreases i, 17int,
    {
        if i <= 0 { 0 }
        else if i == 1 { 1 }
        else {
            Self::dp_acc(i, j, 1, rm)
        }
    }

    
    
    pub open spec fn dp_acc(i: int, j: int, k: int, rm: Seq<i32>) -> int
        recommends 0 <= j < 6, rm.len() == 6,
        decreases i, 16int - k,
    {
        if k < 1 || k > rm[j] as int || k > i || k > 15 { 0 }
        else {
            let p = i - k;
            (
                (if p <= 0 { 1int } else { 0 })
                + Self::dp_val(p, 0, rm) + Self::dp_val(p, 1, rm)
                + Self::dp_val(p, 2, rm) + Self::dp_val(p, 3, rm)
                + Self::dp_val(p, 4, rm) + Self::dp_val(p, 5, rm)
                - Self::dp_val(p, j, rm)
            ) + Self::dp_acc(i, j, k + 1, rm)
        }
    }

    
    pub open spec fn total_val(i: int, rm: Seq<i32>) -> int
        recommends rm.len() == 6,
    {
        if i <= 0 { 1 }
        else {
            Self::dp_val(i, 0, rm) + Self::dp_val(i, 1, rm) + Self::dp_val(i, 2, rm)
                + Self::dp_val(i, 3, rm) + Self::dp_val(i, 4, rm) + Self::dp_val(i, 5, rm)
        }
    }

    pub open spec fn partial_face_sum(i: int, count: int, rm: Seq<i32>) -> int
        decreases count,
    {
        if count <= 0 { 0 }
        else { Self::partial_face_sum(i, count - 1, rm) + Self::dp_val(i, count - 1, rm) }
    }

    proof fn lemma_mod_add(a: int, b: int, m: int)
        requires m > 0, a >= 0, b >= 0,
        ensures (a % m + b % m) % m == (a + b) % m,
    {
        lemma_fundamental_div_mod(a, m);
        lemma_fundamental_div_mod(b, m);
        assert(a + b == m * (a / m + b / m) + (a % m + b % m)) by (nonlinear_arith)
            requires a == m * (a / m) + a % m, b == m * (b / m) + b % m;
        lemma_mod_multiples_vanish(a / m + b / m, a % m + b % m, m);
    }

    proof fn lemma_mod_sub(a: int, b: int, m: int)
        requires a >= 0, b >= 0, a >= b, m > 0,
        ensures (a % m - b % m + m) % m == (a - b) % m,
    {
        lemma_fundamental_div_mod(a, m);
        lemma_fundamental_div_mod(b, m);
        assert(a % m - b % m + m == (a - b) + m * (1 + b / m - a / m)) by (nonlinear_arith)
            requires a == m * (a / m) + a % m, b == m * (b / m) + b % m;
        lemma_mod_multiples_vanish(1 + b / m - a / m, a - b, m);
    }

    #[verifier::spinoff_prover]
    proof fn lemma_dp_val_nonneg(i: int, j: int, rm: Seq<i32>)
        requires 0 <= j < 6, rm.len() == 6,
            forall |l: int| 0 <= l < 6 ==> 1 <= #[trigger] rm[l] <= 15,
        ensures Self::dp_val(i, j, rm) >= 0,
        decreases i, 17int,
    {
        if i <= 0 || i == 1 {}
        else { Self::lemma_dp_acc_nonneg(i, j, 1, rm); }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_dp_acc_nonneg(i: int, j: int, k: int, rm: Seq<i32>)
        requires 0 <= j < 6, rm.len() == 6,
            forall |l: int| 0 <= l < 6 ==> 1 <= #[trigger] rm[l] <= 15,
            k >= 1,
        ensures Self::dp_acc(i, j, k, rm) >= 0,
        decreases i, 16int - k,
    {
        if k < 1 || k > rm[j] as int || k > i || k > 15 {}
        else {
            let p = i - k;
            Self::lemma_dp_val_nonneg(p, 0, rm);
            Self::lemma_dp_val_nonneg(p, 1, rm);
            Self::lemma_dp_val_nonneg(p, 2, rm);
            Self::lemma_dp_val_nonneg(p, 3, rm);
            Self::lemma_dp_val_nonneg(p, 4, rm);
            Self::lemma_dp_val_nonneg(p, 5, rm);
            Self::lemma_dp_acc_nonneg(i, j, k + 1, rm);
        }
    }

    proof fn lemma_total_nonneg(i: int, rm: Seq<i32>)
        requires rm.len() == 6,
            forall |l: int| 0 <= l < 6 ==> 1 <= #[trigger] rm[l] <= 15,
        ensures Self::total_val(i, rm) >= 0,
    {
        if i <= 0 {} else {
            Self::lemma_dp_val_nonneg(i, 0, rm);
            Self::lemma_dp_val_nonneg(i, 1, rm);
            Self::lemma_dp_val_nonneg(i, 2, rm);
            Self::lemma_dp_val_nonneg(i, 3, rm);
            Self::lemma_dp_val_nonneg(i, 4, rm);
            Self::lemma_dp_val_nonneg(i, 5, rm);
        }
    }

    proof fn lemma_total_ge_dp(i: int, j: int, rm: Seq<i32>)
        requires 0 <= j < 6, rm.len() == 6,
            forall |l: int| 0 <= l < 6 ==> 1 <= #[trigger] rm[l] <= 15,
        ensures Self::total_val(i, rm) >= Self::dp_val(i, j, rm),
    {
        if i <= 0 {} else {
            Self::lemma_dp_val_nonneg(i, 0, rm);
            Self::lemma_dp_val_nonneg(i, 1, rm);
            Self::lemma_dp_val_nonneg(i, 2, rm);
            Self::lemma_dp_val_nonneg(i, 3, rm);
            Self::lemma_dp_val_nonneg(i, 4, rm);
            Self::lemma_dp_val_nonneg(i, 5, rm);
        }
    }

    #[verifier::spinoff_prover]
    proof fn lemma_dp_acc_partial_nonneg(i: int, j: int, from_k: int, to_k: int, rm: Seq<i32>)
        requires
            0 <= j < 6, rm.len() == 6,
            forall |l: int| 0 <= l < 6 ==> 1 <= #[trigger] rm[l] <= 15,
            1 <= from_k, from_k <= to_k,
        ensures
            Self::dp_acc(i, j, from_k, rm) >= Self::dp_acc(i, j, to_k, rm),
        decreases to_k - from_k,
    {
        if from_k >= to_k {}
        else if from_k > rm[j] as int || from_k > i || from_k > 15 {
        } else {
            let p = i - from_k;
            Self::lemma_dp_val_nonneg(p, 0, rm);
            Self::lemma_dp_val_nonneg(p, 1, rm);
            Self::lemma_dp_val_nonneg(p, 2, rm);
            Self::lemma_dp_val_nonneg(p, 3, rm);
            Self::lemma_dp_val_nonneg(p, 4, rm);
            Self::lemma_dp_val_nonneg(p, 5, rm);
            Self::lemma_dp_acc_partial_nonneg(i, j, from_k + 1, to_k, rm);
        }
    }

    proof fn lemma_partial_nonneg(i: int, count: int, rm: Seq<i32>)
        requires 0 <= count <= 6, rm.len() == 6,
            forall |l: int| 0 <= l < 6 ==> 1 <= #[trigger] rm[l] <= 15,
        ensures Self::partial_face_sum(i, count, rm) >= 0,
        decreases count,
    {
        if count <= 0 {}
        else {
            Self::lemma_partial_nonneg(i, count - 1, rm);
            Self::lemma_dp_val_nonneg(i, count - 1, rm);
        }
    }

    proof fn lemma_partial_eq_total(i: int, rm: Seq<i32>)
        requires i > 0, rm.len() == 6,
        ensures Self::partial_face_sum(i, 6, rm) == Self::total_val(i, rm),
    {
        reveal_with_fuel(Solution::partial_face_sum, 7);
    }

    proof fn lemma_dp_acc_unfold(i: int, j: int, k: int, rm: Seq<i32>)
        requires
            0 <= j < 6, rm.len() == 6,
            forall |l: int| 0 <= l < 6 ==> 1 <= #[trigger] rm[l] <= 15,
            k >= 1, k <= rm[j] as int, k <= i, k <= 15,
        ensures
            Self::dp_acc(i, j, k, rm) - Self::dp_acc(i, j, k + 1, rm)
                == Self::total_val(i - k, rm) - Self::dp_val(i - k, j, rm),
    {
        let p = i - k;
        if p <= 0 {
            assert(Self::dp_val(p, 0, rm) == 0);
            assert(Self::dp_val(p, 1, rm) == 0);
            assert(Self::dp_val(p, 2, rm) == 0);
            assert(Self::dp_val(p, 3, rm) == 0);
            assert(Self::dp_val(p, 4, rm) == 0);
            assert(Self::dp_val(p, 5, rm) == 0);
            assert(Self::total_val(p, rm) == 1);
        }
    }

    proof fn lemma_index_unique6(i1: int, j1: int, i2: int, j2: int)
        requires
            0 <= j1 < 6, 0 <= j2 < 6,
            i1 * 6 + j1 == i2 * 6 + j2,
        ensures
            i1 == i2, j1 == j2,
    {
        assert(i1 == i2 && j1 == j2) by (nonlinear_arith)
            requires 0 <= j1 < 6, 0 <= j2 < 6, i1 * 6 + j1 == i2 * 6 + j2;
    }

    #[verifier::spinoff_prover]
    pub fn die_simulator(n: i32, roll_max: Vec<i32>) -> (result: i32)
        requires
            1 <= n <= 5000,
            roll_max.len() == 6,
            forall |j: int| 0 <= j < 6 ==> 1 <= #[trigger] roll_max[j] <= 15,
        ensures
            0 <= result < 1_000_000_007,
            result as int == Solution::total_val(n as int, roll_max@) % 1_000_000_007,
    {
        let modp: i64 = 1_000_000_007;
        let n_us = n as usize;
        let dp_size = (n_us + 1) * 6;
        let ghost rm = roll_max@;
        let ghost M: int = 1_000_000_007int;
        let mut dp: Vec<i64> = Vec::new();
        let mut idx = 0usize;
        while idx < dp_size
            invariant
                dp@.len() == idx as int,
                idx <= dp_size,
                dp_size == (n_us + 1) * 6,
                n_us == n as usize,
                1 <= n <= 5000,
                forall |k: int| 0 <= k < idx as int ==> dp@[k] == 0i64,
            decreases dp_size - idx
        {
            dp.push(0i64);
            idx = idx + 1;
        }
        let mut total: Vec<i64> = Vec::new();
        idx = 0;
        while idx <= n_us
            invariant
                total@.len() == idx as int,
                idx <= n_us + 1,
                n_us == n as usize,
                1 <= n <= 5000,
                forall |k: int| 0 <= k < idx as int ==> total@[k] == 0i64,
            decreases n_us + 1 - idx
        {
            total.push(0i64);
            idx = idx + 1;
        }
        total.set(0, 1);
        let mut j = 0usize;
        while j < 6
            invariant
                0 <= j <= 6,
                dp@.len() == dp_size as int,
                dp_size == (n_us + 1) * 6,
                n_us >= 1,
                n_us == n as usize,
                1 <= n <= 5000,
                total@.len() == n_us as int + 1,
                forall |jj: int| 0 <= jj < j as int ==> (#[trigger] dp@[6 + jj]) == 1i64,
                forall |k: int| 0 <= k < 6 ==> dp@[k] == 0i64,
                forall |jj: int| j as int <= jj < 6 ==> (#[trigger] dp@[6 + jj]) == 0i64,
                forall |k: int| 12 <= k < dp@.len() ==> dp@[k] == 0i64,
                total@[0] == 1i64,
                forall |k: int| 1 <= k < total@.len() ==> total@[k] == 0i64,
            decreases 6 - j
        {
            dp.set(6 + j, 1);
            j = j + 1;
        }
        total.set(1, 6);
        proof {
            assert forall |ii: int, jj: int| 0 <= ii < 2 && 0 <= jj < 6
                implies (#[trigger] dp@[ii * 6 + jj]) as int
                    == Self::dp_val(ii, jj, rm) % M
                    && 0 <= dp@[ii * 6 + jj]
                    && dp@[ii * 6 + jj] < M
            by {
                assert(0 <= ii * 6 + jj && ii * 6 + jj < 12) by (nonlinear_arith)
                    requires 0 <= ii < 2, 0 <= jj < 6;
                if ii == 0 {
                    assert(dp@[jj] == 0i64);
                    assert(Self::dp_val(0, jj, rm) == 0);
                } else {
                    assert(dp@[6 + jj] == 1i64);
                    assert(Self::dp_val(1, jj, rm) == 1);
                }
            };
            assert forall |ii: int| 0 <= ii < 2
                implies (#[trigger] total@[ii]) as int
                    == Self::total_val(ii, rm) % M
                    && 0 <= total@[ii]
                    && total@[ii] < M
            by {
                if ii == 0 {
                    assert(total@[0] == 1i64);
                    assert(Self::total_val(0, rm) == 1);
                } else {
                    assert(total@[1] == 6i64);
                    assert(Self::dp_val(1, 0, rm) == 1);
                    assert(Self::dp_val(1, 1, rm) == 1);
                    assert(Self::dp_val(1, 2, rm) == 1);
                    assert(Self::dp_val(1, 3, rm) == 1);
                    assert(Self::dp_val(1, 4, rm) == 1);
                    assert(Self::dp_val(1, 5, rm) == 1);
                }
            };
        }
        let mut i = 2usize;
        while i <= n_us
            invariant
                2 <= i <= n_us + 1,
                n_us == n as usize,
                1 <= n <= 5000,
                dp@.len() == dp_size as int,
                dp_size == (n_us + 1) * 6,
                total@.len() == n_us as int + 1,
                roll_max@.len() == 6,
                rm == roll_max@,
                M == 1_000_000_007int,
                modp == 1_000_000_007i64,
                forall |l: int| 0 <= l < 6 ==> 1 <= #[trigger] rm[l] <= 15,
                forall |ii: int, jj: int| 0 <= ii < i as int && 0 <= jj < 6 ==>
                    (#[trigger] dp@[ii * 6 + jj]) as int
                        == Self::dp_val(ii, jj, rm) % M
                    && 0 <= dp@[ii * 6 + jj]
                    && dp@[ii * 6 + jj] < M,
                forall |ii: int| 0 <= ii < i as int ==>
                    (#[trigger] total@[ii]) as int
                        == Self::total_val(ii, rm) % M
                    && 0 <= total@[ii]
                    && total@[ii] < M,
            decreases n_us + 1 - i
        {
            let mut j = 0usize;
            while j < 6
                invariant
                    0 <= j <= 6,
                    2 <= i <= n_us,
                    n_us == n as usize,
                    1 <= n <= 5000,
                    dp@.len() == dp_size as int,
                    dp_size == (n_us + 1) * 6,
                    total@.len() == n_us as int + 1,
                    roll_max@.len() == 6,
                    rm == roll_max@,
                    M == 1_000_000_007int,
                    modp == 1_000_000_007i64,
                    forall |l: int| 0 <= l < 6 ==> 1 <= #[trigger] rm[l] <= 15,
                    forall |ii: int, jj: int| 0 <= ii < i as int && 0 <= jj < 6 ==>
                        (#[trigger] dp@[ii * 6 + jj]) as int
                            == Self::dp_val(ii, jj, rm) % M
                        && 0 <= dp@[ii * 6 + jj]
                        && dp@[ii * 6 + jj] < M,
                    forall |jj: int| 0 <= jj < j as int ==>
                        (#[trigger] dp@[i as int * 6 + jj]) as int
                            == Self::dp_val(i as int, jj, rm) % M
                        && 0 <= dp@[i as int * 6 + jj]
                        && dp@[i as int * 6 + jj] < M,
                    forall |ii: int| 0 <= ii < i as int ==>
                        (#[trigger] total@[ii]) as int
                            == Self::total_val(ii, rm) % M
                        && 0 <= total@[ii]
                        && total@[ii] < M,
                decreases 6 - j
            {
                let rm_j = roll_max[j] as usize;
                let bound = if rm_j < i { rm_j } else { i };
                let mut val: i64 = 0;
                let mut k = 1usize;
                while k <= bound
                    invariant
                        1 <= k <= bound + 1,
                        bound == (if rm_j < i { rm_j } else { i }),
                        rm_j == roll_max@[j as int] as usize,
                        0 <= j < 6,
                        2 <= i <= n_us,
                        n_us == n as usize,
                        1 <= n <= 5000,
                        dp@.len() == dp_size as int,
                        dp_size == (n_us + 1) * 6,
                        total@.len() == n_us as int + 1,
                        roll_max@.len() == 6,
                        rm == roll_max@,
                        M == 1_000_000_007int,
                        modp == 1_000_000_007i64,
                        forall |l: int| 0 <= l < 6 ==> 1 <= #[trigger] rm[l] <= 15,
                        forall |ii: int, jj: int| 0 <= ii < i as int && 0 <= jj < 6 ==>
                            (#[trigger] dp@[ii * 6 + jj]) as int
                                == Self::dp_val(ii, jj, rm) % M
                            && 0 <= dp@[ii * 6 + jj]
                            && dp@[ii * 6 + jj] < M,
                        forall |ii: int| 0 <= ii < i as int ==>
                            (#[trigger] total@[ii]) as int
                                == Self::total_val(ii, rm) % M
                            && 0 <= total@[ii]
                            && total@[ii] < M,
                        0 <= val < 1_000_000_007i64,
                        val as int == (Self::dp_acc(i as int, j as int, 1, rm)
                            - Self::dp_acc(i as int, j as int, k as int, rm)) % M,
                    decreases bound + 1 - k
                {
                    let prev = i - k;
                    proof {
                        let ii = i as int;
                        let jj = j as int;
                        let kk = k as int;
                        let pp = prev as int;
                        assert(pp == ii - kk);
                        assert(0 <= pp && pp < ii);
                        let dplen = dp@.len() as int;
                        let nus = n_us as int;
                        assert(0 <= pp * 6 + jj && pp * 6 + jj < dplen)
                            by (nonlinear_arith)
                            requires 0 <= pp, pp < ii, ii <= nus,
                                0 <= jj < 6, dplen == (nus + 1) * 6;
                        let tv = Self::total_val(pp, rm);
                        let dv = Self::dp_val(pp, jj, rm);
                        Self::lemma_total_nonneg(pp, rm);
                        Self::lemma_total_ge_dp(pp, jj, rm);
                        Self::lemma_dp_val_nonneg(pp, jj, rm);
                        assert(total@[pp] as int == tv % M);
                        assert(dp@[pp * 6 + jj] as int == dv % M);
                        Self::lemma_mod_sub(tv, dv, M);
                        let old_diff = Self::dp_acc(ii, jj, 1, rm)
                            - Self::dp_acc(ii, jj, kk, rm);
                        Self::lemma_dp_acc_partial_nonneg(ii, jj, 1, kk, rm);
                        assert(old_diff >= 0);
                        assert(kk >= 1 && kk <= rm[jj] as int && kk <= ii && kk <= 15) by {
                            assert(kk <= bound as int);
                            if rm_j < i {
                                assert(bound == rm_j);
                                assert(kk <= rm_j as int);
                                assert(rm_j == rm[jj] as usize);
                            } else {
                                assert(bound == i);
                                assert(kk <= ii);
                            }
                            assert(rm[jj] <= 15);
                        };
                        Self::lemma_dp_acc_unfold(ii, jj, kk, rm);
                        let step_val = tv - dv;
                        assert(step_val >= 0);
                        Self::lemma_mod_add(old_diff, step_val, M);
                        assert(old_diff + step_val
                            == Self::dp_acc(ii, jj, 1, rm)
                                - Self::dp_acc(ii, jj, kk + 1, rm));
                    }
                    let diff = (total[prev] - dp[prev * 6 + j] + modp) % modp;
                    val = (val + diff) % modp;
                    k = k + 1;
                }
                proof {
                    let ii = i as int;
                    let jj = j as int;
                    assert(Self::dp_acc(ii, jj, k as int, rm) == 0int);
                    assert(val as int == Self::dp_acc(ii, jj, 1, rm) % M);
                    assert(Self::dp_val(ii, jj, rm) == Self::dp_acc(ii, jj, 1, rm));
                    assert(val as int == Self::dp_val(ii, jj, rm) % M);
                    let dplen = dp@.len() as int;
                    let nus = n_us as int;
                    assert(0 <= ii * 6 + jj && ii * 6 + jj < dplen)
                        by (nonlinear_arith)
                        requires 0 <= ii, ii <= nus, 0 <= jj < 6,
                            dplen == (nus + 1) * 6;
                }
                dp.set(i * 6 + j, val);
                proof {
                    let ii = i as int;
                    let jj = j as int;
                    assert forall |i2: int, j2: int|
                        0 <= i2 < ii && 0 <= j2 < 6
                        implies (#[trigger] dp@[i2 * 6 + j2]) as int
                            == Self::dp_val(i2, j2, rm) % M
                            && 0 <= dp@[i2 * 6 + j2]
                            && dp@[i2 * 6 + j2] < M
                    by {
                        if i2 * 6 + j2 == ii * 6 + jj {
                            Self::lemma_index_unique6(i2, j2, ii, jj);
                        }
                    };
                    assert forall |j2: int| 0 <= j2 <= jj
                        implies (#[trigger] dp@[ii * 6 + j2]) as int
                            == Self::dp_val(ii, j2, rm) % M
                            && 0 <= dp@[ii * 6 + j2]
                            && dp@[ii * 6 + j2] < M
                    by {
                        if ii * 6 + j2 == ii * 6 + jj {
                            assert(j2 == jj);
                        }
                    };
                }
                j = j + 1;
            }
            let mut t: i64 = 0;
            let mut j2 = 0usize;
            while j2 < 6
                invariant
                    0 <= j2 <= 6,
                    2 <= i <= n_us,
                    n_us == n as usize,
                    1 <= n <= 5000,
                    dp@.len() == dp_size as int,
                    dp_size == (n_us + 1) * 6,
                    total@.len() == n_us as int + 1,
                    roll_max@.len() == 6,
                    rm == roll_max@,
                    M == 1_000_000_007int,
                    modp == 1_000_000_007i64,
                    forall |l: int| 0 <= l < 6 ==> 1 <= #[trigger] rm[l] <= 15,
                    forall |jj: int| 0 <= jj < 6 ==>
                        (#[trigger] dp@[i as int * 6 + jj]) as int
                            == Self::dp_val(i as int, jj, rm) % M
                        && 0 <= dp@[i as int * 6 + jj]
                        && dp@[i as int * 6 + jj] < M,
                    forall |ii: int, jj: int| 0 <= ii < i as int && 0 <= jj < 6 ==>
                        (#[trigger] dp@[ii * 6 + jj]) as int
                            == Self::dp_val(ii, jj, rm) % M
                        && 0 <= dp@[ii * 6 + jj]
                        && dp@[ii * 6 + jj] < M,
                    forall |ii: int| 0 <= ii < i as int ==>
                        (#[trigger] total@[ii]) as int
                            == Self::total_val(ii, rm) % M
                        && 0 <= total@[ii]
                        && total@[ii] < M,
                    0 <= t < 1_000_000_007i64,
                    t as int == Self::partial_face_sum(i as int, j2 as int, rm) % M,
                decreases 6 - j2
            {
                proof {
                    let pfs = Self::partial_face_sum(i as int, j2 as int, rm);
                    let dpv = Self::dp_val(i as int, j2 as int, rm);
                    Self::lemma_partial_nonneg(i as int, j2 as int, rm);
                    Self::lemma_dp_val_nonneg(i as int, j2 as int, rm);
                    Self::lemma_mod_add(pfs, dpv, M);
                    let ci = i as int;
                    let cj2 = j2 as int;
                    let dplen = dp@.len() as int;
                    let nus = n_us as int;
                    assert(0 <= ci * 6 + cj2 && ci * 6 + cj2 < dplen)
                        by (nonlinear_arith)
                        requires 0 <= ci, ci <= nus,
                            0 <= cj2 < 6,
                            dplen == (nus + 1) * 6;
                }
                t = (t + dp[i * 6 + j2]) % modp;
                j2 = j2 + 1;
            }
            proof {
                Self::lemma_partial_eq_total(i as int, rm);
                assert(t as int == Self::total_val(i as int, rm) % M);
            }
            total.set(i, t);
            proof {
                let ii = i as int;
                assert forall |i2: int, j2: int|
                    0 <= i2 <= ii && 0 <= j2 < 6
                    implies (#[trigger] dp@[i2 * 6 + j2]) as int
                        == Self::dp_val(i2, j2, rm) % M
                        && 0 <= dp@[i2 * 6 + j2]
                        && dp@[i2 * 6 + j2] < M
                by {};
                assert forall |i2: int| 0 <= i2 <= ii
                    implies (#[trigger] total@[i2]) as int
                        == Self::total_val(i2, rm) % M
                        && 0 <= total@[i2]
                        && total@[i2] < M
                by {
                    if i2 < ii {
                    } else {
                        assert(total@[ii] == t);
                    }
                };
            }
            i = i + 1;
        }
        (total[n_us] % modp) as i32
    }
}

}
