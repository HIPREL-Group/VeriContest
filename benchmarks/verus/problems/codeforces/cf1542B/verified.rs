use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn pow_int(a: int, k: int) -> int
    decreases k,
{
    if k <= 0 {
        1int
    } else {
        a * pow_int(a, k - 1)
    }
}

pub open spec fn in_generated_set(n: int, a: int, b: int) -> bool {
    (a == 1 && (n - 1) % b == 0) || (a > 1 && exists|k: int|
        k >= 0 && #[trigger] pow_int(a, k) <= n && (n - pow_int(a, k)) % b == 0)
}

proof fn lemma_pow_int_ge_1(a: int, k: int)
    requires
        a >= 2,
        k >= 0,
    ensures
        pow_int(a, k) >= 1,
    decreases k,
{
    if k == 0 {
        assert(pow_int(a, k) == 1);
    } else {
        lemma_pow_int_ge_1(a, (k - 1) as int);
        assert(pow_int(a, k) == a * pow_int(a, k - 1));
        assert(pow_int(a, k - 1) >= 1);
        assert(a * pow_int(a, k - 1) >= 2) by (nonlinear_arith)
            requires
                a >= 2,
                pow_int(a, k - 1) >= 1,
        {
        }
    }
}

proof fn lemma_pow_int_succ(a: int, k: int)
    requires
        k >= 0,
    ensures
        pow_int(a, k + 1) == a * pow_int(a, k),
{
    assert(pow_int(a, k + 1) == a * pow_int(a, (k + 1) - 1));
    assert((k + 1) - 1 == k);
}

proof fn lemma_pow_int_mono(a: int, m2: int, m1: int)
    requires
        a >= 2,
        0 <= m1,
        m1 <= m2,
    ensures
        pow_int(a, m1) <= pow_int(a, m2),
    decreases m2 - m1,
{
    if m1 == m2 {
    } else {
        lemma_pow_int_mono(a, (m2 - 1) as int, m1);
        lemma_pow_int_succ(a, (m2 - 1) as int);
        assert(pow_int(a, m2) == a * pow_int(a, m2 - 1));
        assert(pow_int(a, m2 - 1) >= pow_int(a, m1));
        lemma_pow_int_ge_1(a, m1);
        assert(a * pow_int(a, m2 - 1) >= 2 * pow_int(a, m1)) by (nonlinear_arith)
            requires
                a >= 2,
                pow_int(a, m2 - 1) >= pow_int(a, m1),
                pow_int(a, m1) >= 1,
        {
        }
        assert(2 * pow_int(a, m1) >= pow_int(a, m1)) by (nonlinear_arith)
            requires
                pow_int(a, m1) >= 1,
        {
        }
    }
}

proof fn lemma_pow_mul_gt_n(n: int, a: int, pow: int)
    requires
        1 <= n <= 1_000_000_000,
        2 <= a <= 1_000_000_000,
        1 <= pow <= n,
        pow > n / a,
    ensures
        pow * a > n,
{
    assert(pow * a > n) by (nonlinear_arith)
        requires
            1 <= n <= 1_000_000_000,
            2 <= a <= 1_000_000_000,
            1 <= pow <= n,
            pow > n / a,
    {
    }
}

proof fn lemma_pow_mul_le_n_i64(pow: i64, a: i64, n: i64)
    requires
        1 <= n <= 1_000_000_000,
        1 <= pow <= n,
        2 <= a <= 1_000_000_000,
        pow <= n / a,
    ensures
        pow * a <= n,
        pow * a <= 1_000_000_000,
{
    assert(pow * a <= n) by (nonlinear_arith)
        requires
            1 <= n <= 1_000_000_000,
            pow <= n / a,
            2 <= a <= 1_000_000_000,
            1 <= pow <= n,
    {
    }
    assert(pow * a <= 1_000_000_000);
}

proof fn lemma_n_pow_decreases(n: i64, old_pow: i64, a: i64)
    requires
        1 <= n <= 1_000_000_000,
        1 <= old_pow <= n,
        2 <= a <= 1_000_000_000,
        old_pow <= n / a,
    ensures
        n - old_pow * a < n - old_pow,
{
    lemma_pow_mul_le_n_i64(old_pow, a, n);
    assert(old_pow * a <= n);
    assert(n - old_pow * a < n - old_pow) by (nonlinear_arith)
        requires
            1 <= old_pow <= n,
            2 <= a,
            old_pow * a <= n,
    {
    }
}

proof fn lemma_j_le_k_max(n: int, a: int, j: int, k: int)
    requires
        a >= 2,
        k >= 0,
        pow_int(a, k + 1) > n,
        j >= 0,
        pow_int(a, j) <= n,
    ensures
        j <= k,
{
    if j > k {
        lemma_pow_int_mono(a, j, k + 1);
        assert(pow_int(a, j) >= pow_int(a, k + 1));
        assert(pow_int(a, j) > n);
        assert(false);
    }
}

proof fn lemma_j_lt_k_when_pow_exceeds_n(n: int, a: int, j: int, k: int)
    requires
        a >= 2,
        k >= 0,
        pow_int(a, k) > n,
        j >= 0,
        pow_int(a, j) <= n,
    ensures
        j < k,
{
    if j >= k {
        lemma_pow_int_mono(a, j, k);
        assert(pow_int(a, j) >= pow_int(a, k));
        assert(pow_int(a, j) > n);
        assert(false);
    }
}

proof fn lemma_forall_pow_fails_implies_not_in_set(n: int, a: int, b: int)
    requires
        a >= 2,
        b >= 1,
        forall|j: int|
            j >= 0 && pow_int(a, j) <= n ==> (n - pow_int(a, j)) % b != 0,
    ensures
        !in_generated_set(n, a, b),
{
    assert(!exists|k: int|
        k >= 0 && #[trigger] pow_int(a, k) <= n && (n - pow_int(a, k)) % b == 0);
}

proof fn lemma_forall_from_div_branch(
    n: int,
    a: int,
    b: int,
    k: int,
)
    requires
        a >= 2,
        k >= 0,
        pow_int(a, k) <= n,
        (n - pow_int(a, k)) % b != 0,
        pow_int(a, k + 1) > n,
        forall|i: int| 0 <= i && i < k ==> (n - pow_int(a, i)) % b != 0,
    ensures
        forall|j: int|
            j >= 0 && pow_int(a, j) <= n ==> (n - pow_int(a, j)) % b != 0,
{
    assert forall|j: int| j >= 0 && pow_int(a, j) <= n implies (n - pow_int(a, j)) % b != 0 by {
        lemma_j_le_k_max(n, a, j, k);
        assert(j <= k);
        if j < k {
            assert((n - pow_int(a, j)) % b != 0);
        } else {
            assert(j == k);
            assert((n - pow_int(a, k)) % b != 0);
        }
    };
}

proof fn lemma_forall_from_exit_branch(
    n: int,
    a: int,
    b: int,
    k: int,
)
    requires
        a >= 2,
        k >= 0,
        pow_int(a, k) > n,
        forall|i: int| 0 <= i && i < k ==> (n - pow_int(a, i)) % b != 0,
    ensures
        forall|j: int|
            j >= 0 && pow_int(a, j) <= n ==> (n - pow_int(a, j)) % b != 0,
{
    assert forall|j: int| j >= 0 && pow_int(a, j) <= n implies (n - pow_int(a, j)) % b != 0 by {
        lemma_j_lt_k_when_pow_exceeds_n(n, a, j, k);
        assert(j < k);
        assert((n - pow_int(a, j)) % b != 0);
    };
}

impl Solution {
    pub fn n_in_generated_set(n: i64, a: i64, b: i64) -> (res: bool)
        requires
            1 <= n <= 1_000_000_000,
            1 <= a <= 1_000_000_000,
            1 <= b <= 1_000_000_000,
        ensures
            res == in_generated_set(n as int, a as int, b as int),
    {
        if a == 1 {
            proof {
                assert(in_generated_set(n as int, 1, b as int) == ((n as int - 1) % (b as int) == 0));
            }
            (n - 1) % b == 0
        } else {
            let mut pow: i64 = 1;
            let ghost mut k: int = 0;
            while pow <= n
                invariant
                    2 <= a <= 1_000_000_000,
                    1 <= n <= 1_000_000_000,
                    1 <= b <= 1_000_000_000,
                    k >= 0,
                    pow as int == pow_int(a as int, k),
                    pow as int <= n as int,
                    forall|j: int|
                        0 <= j && j < k ==> (n as int - pow_int(a as int, j)) % (b as int) != 0,
                decreases n - pow
            {
                proof {
                    lemma_pow_int_ge_1(a as int, k);
                }
                if (n - pow) % b == 0 {
                    proof {
                        assert((n as int - pow_int(a as int, k)) % (b as int) == 0);
                        assert(pow_int(a as int, k) <= n as int);
                        assert(in_generated_set(n as int, a as int, b as int));
                    }
                    return true;
                }
                assert((n as int - pow_int(a as int, k)) % (b as int) != 0);
                if pow > n / a {
                    proof {
                        assert(pow_int(a as int, k + 1) > n as int) by {
                            lemma_pow_int_succ(a as int, k);
                            assert(pow_int(a as int, k + 1) == (a as int) * pow_int(a as int, k));
                            lemma_pow_mul_gt_n(n as int, a as int, pow as int);
                            assert((a as int) * pow_int(a as int, k) > n as int);
                        };
                        lemma_forall_from_div_branch(
                            n as int,
                            a as int,
                            b as int,
                            k,
                        );
                        lemma_forall_pow_fails_implies_not_in_set(
                            n as int,
                            a as int,
                            b as int,
                        );
                        assert(!in_generated_set(n as int, a as int, b as int));
                    }
                    return false;
                }
                proof {
                    lemma_pow_mul_le_n_i64(pow, a, n);
                    lemma_n_pow_decreases(n, pow, a);
                }
                pow = pow * a;
                proof {
                    lemma_pow_int_succ(a as int, k);
                    assert(pow as int == pow_int(a as int, k + 1));
                    assert(forall|j: int|
                        0 <= j && j < k + 1 ==> (n as int - pow_int(a as int, j)) % (b as int)
                            != 0);
                    k = k + 1;
                }
            }
            proof {
                assert(pow as int > n as int);
                assert(pow as int == pow_int(a as int, k));
                lemma_forall_from_exit_branch(n as int, a as int, b as int, k);
                lemma_forall_pow_fails_implies_not_in_set(n as int, a as int, b as int);
                assert(!in_generated_set(n as int, a as int, b as int));
            }
            false
        }
    }
}

}
