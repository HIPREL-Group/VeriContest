use vstd::prelude::*;
use vstd::arithmetic::div_mod::{lemma_fundamental_div_mod, lemma_mod_multiples_vanish};

fn main() {}

verus! {

pub struct Solution;

pub open spec fn pow2(n: nat) -> int
    decreases n,
{
    if n == 0 {
        1
    } else {
        2 * pow2((n - 1) as nat)
    }
}

pub open spec fn num_bits(n: int) -> nat
    decreases n,
{
    if n <= 0 {
        0
    } else {
        1 + num_bits(n / 2)
    }
}

pub open spec fn concat_value(n: int) -> int
    decreases n,
{
    if n <= 0 {
        0
    } else {
        concat_value(n - 1) * pow2(num_bits(n)) + n
    }
}

proof fn pow2_positive(n: nat)
    ensures
        pow2(n) > 0,
    decreases n,
{
    if n > 0 {
        pow2_positive((n - 1) as nat);
    }
}

proof fn num_bits_pow2(k: nat)
    ensures
        num_bits(pow2(k)) == k + 1,
    decreases k,
{
    pow2_positive(k);
    if k == 0 {
        assert(pow2(0nat) == 1int);
        assert(num_bits(1int) == 1 + num_bits(0int));
        assert(num_bits(0int) == 0nat);
    } else {
        pow2_positive((k - 1) as nat);
        assert(pow2(k) == 2 * pow2((k - 1) as nat));
        assert(pow2(k) > 0);
        assert(pow2(k) / 2 == pow2((k - 1) as nat)) by(nonlinear_arith)
            requires
                pow2(k) == 2 * pow2((k - 1) as nat),
                pow2((k - 1) as nat) > 0,
        ;
        num_bits_pow2((k - 1) as nat);
        assert(num_bits(pow2(k)) == 1 + num_bits(pow2(k) / 2));
        assert(num_bits(pow2(k) / 2) == num_bits(pow2((k - 1) as nat)));
    }
}

proof fn num_bits_upper(n: int)
    requires
        n > 0,
    ensures
        n < pow2(num_bits(n)),
    decreases n,
{
    if n == 1 {
        assert(num_bits(1int) == 1 + num_bits(0int));
        assert(num_bits(0int) == 0nat);
        assert(pow2(1nat) == 2 * pow2(0nat));
        assert(pow2(0nat) == 1int);
    } else {
        num_bits_upper(n / 2);
        pow2_positive(num_bits(n / 2));
        let k = num_bits(n / 2);
        assert(num_bits(n) == 1 + k);
        assert(pow2((1 + k) as nat) == 2 * pow2(k));
        assert(n <= 2 * (n / 2) + 1);
        assert(n < 2 * pow2(k)) by(nonlinear_arith)
            requires
                n / 2 < pow2(k),
                n <= 2 * (n / 2) + 1,
                pow2(k) > 0,
        ;
    }
}

proof fn num_bits_lower(n: int)
    requires
        n > 0,
    ensures
        pow2((num_bits(n) - 1) as nat) <= n,
    decreases n,
{
    if n == 1 {
        assert(num_bits(1int) == 1 + num_bits(0int));
        assert(num_bits(0int) == 0nat);
        assert(pow2(0nat) == 1int);
    } else {
        num_bits_lower(n / 2);
        pow2_positive((num_bits(n / 2) - 1) as nat);
        let k = num_bits(n / 2);
        assert(num_bits(n) == 1 + k);
        assert(pow2(k) == 2 * pow2((k - 1) as nat));
        assert(2 * (n / 2) <= n);
        assert(2 * pow2((k - 1) as nat) <= n) by(nonlinear_arith)
            requires
                pow2((k - 1) as nat) <= n / 2,
                2 * (n / 2) <= n,
        ;
    }
}

proof fn pow2_mono(a: nat, b: nat)
    requires
        a <= b,
    ensures
        pow2(a) <= pow2(b),
    decreases b - a,
{
    if a < b {
        pow2_mono(a, (b - 1) as nat);
        pow2_positive((b - 1) as nat);
    }
}

proof fn num_bits_bounded(n: int, bound: nat)
    requires
        0 < n,
        n < pow2(bound),
    ensures
        num_bits(n) <= bound,
{
    num_bits_lower(n);
    if num_bits(n) > bound {
        pow2_mono(bound, (num_bits(n) - 1) as nat);
    }
}

proof fn num_bits_step_same(i: int)
    requires
        i > 1,
        i < pow2(num_bits(i - 1) as nat),
    ensures
        num_bits(i) == num_bits(i - 1),
    decreases i,
{
    if i % 2 == 1 {
        assert(i / 2 == (i - 1) / 2);
    } else {
        let k = i / 2;
        assert(i == 2 * k) by(nonlinear_arith)
            requires
                i % 2 == 0,
                k == i / 2,
        ;
        assert((i - 1) / 2 == k - 1) by(nonlinear_arith)
            requires
                i == 2 * k,
                k >= 1,
        ;
        let b = num_bits(k - 1);
        assert(num_bits(i - 1) == 1 + b);
        assert(pow2((1 + b) as nat) == 2 * pow2(b));
        assert(i < 2 * pow2(b));
        assert(k < pow2(b)) by(nonlinear_arith)
            requires
                i < 2 * pow2(b),
                i == 2 * k,
        ;
        if k == 1 {
            assert(b == num_bits(0int));
            assert(num_bits(0int) == 0nat);
            assert(pow2(0nat) == 1int);
            assert(false) by(nonlinear_arith)
                requires
                    k < 1int,
                    k == 1,
            ;
        } else {
            num_bits_step_same(k);
        }
    }
}

proof fn num_bits_step_inc(i: int)
    requires
        i > 0,
        i == pow2(num_bits(i - 1) as nat),
    ensures
        num_bits(i) == num_bits(i - 1) + 1,
{
    let k = num_bits(i - 1);
    num_bits_pow2(k);
}

proof fn mod_mul_add(a: int, b: int, c: int, m: int)
    requires
        m > 0,
    ensures
        ((a % m) * b + c) % m == (a * b + c) % m,
{
    lemma_fundamental_div_mod(a, m);
    let q = a / m;
    let r = a % m;
    assert(a * b + c == (r * b + c) + q * b * m) by(nonlinear_arith)
        requires
            a == q * m + r,
    ;
    lemma_mod_multiples_vanish(q * b, r * b + c, m);
}

proof fn pow2_17_value()
    ensures
        pow2(17nat) == 131_072,
{
    assert(pow2(0nat) == 1int);
    assert(pow2(1nat) == 2int);
    assert(pow2(2nat) == 4int);
    assert(pow2(3nat) == 8int);
    assert(pow2(4nat) == 16int);
    assert(pow2(5nat) == 32int);
    assert(pow2(6nat) == 64int);
    assert(pow2(7nat) == 128int);
    assert(pow2(8nat) == 256int);
    assert(pow2(9nat) == 512int);
    assert(pow2(10nat) == 1024int);
    assert(pow2(11nat) == 2048int);
    assert(pow2(12nat) == 4096int);
    assert(pow2(13nat) == 8192int);
    assert(pow2(14nat) == 16384int);
    assert(pow2(15nat) == 32768int);
    assert(pow2(16nat) == 65536int);
    assert(pow2(17nat) == 131072int);
}

impl Solution {
    pub fn concatenated_binary(n: i32) -> (result: i32)
        requires
            1 <= n <= 100_000,
        ensures
            0 <= result < 1_000_000_007,
            result as int == concat_value(n as int) % 1_000_000_007,
    {
        let modulo: i64 = 1_000_000_007;
        let mut ans: i64 = 0;
        let mut shift: i64 = 1;
        let mut i: i32 = 1;

        proof {
            assert(num_bits(0int) == 0nat);
            assert(pow2(0nat) == 1int);
            assert(concat_value(0int) == 0int);
        }

        while i <= n
            invariant
                1 <= i <= n + 1,
                1 <= n <= 100_000,
                modulo == 1_000_000_007i64,
                0 <= ans < modulo,
                shift as int == pow2(num_bits((i - 1) as int) as nat),
                1 <= shift <= 131_072,
                ans as int == concat_value((i - 1) as int) % 1_000_000_007,
            decreases n - i + 1,
        {
            if i as i64 == shift {
                proof {
                    num_bits_step_inc(i as int);
                    pow2_positive(num_bits(i as int) as nat);
                    let nb = num_bits(i as int);
                    assert(pow2(nb) == 2 * pow2((nb - 1) as nat));
                    num_bits_upper(i as int);
                    pow2_17_value();
                    num_bits_bounded(i as int, 17nat);
                    pow2_mono(nb, 17nat);
                }
                shift = shift * 2;
            } else {
                proof {
                    num_bits_upper((i - 1) as int);
                    num_bits_step_same(i as int);
                }
            }

            proof {
                mod_mul_add(
                    concat_value((i - 1) as int),
                    pow2(num_bits(i as int) as nat),
                    i as int,
                    1_000_000_007,
                );
            }

            let ghost ga = ans as int;
            let ghost gs = shift as int;
            let ghost gi = i as int;

            proof {
                assert(ga * gs + gi < 140_000_000_000_000int) by(nonlinear_arith)
                    requires
                        0 <= ga <= 1_000_000_006,
                        1 <= gs <= 131_072,
                        1 <= gi <= 100_000,
                ;
            }

            ans = (ans * shift + i as i64) % modulo;
            i += 1;

            proof {
                if i <= n {
                    pow2_17_value();
                    assert(100_000 < 131_072int);
                    num_bits_upper((i - 1) as int);
                    num_bits_bounded((i - 1) as int, 17nat);
                    pow2_mono(num_bits((i - 1) as int) as nat, 17nat);
                }
            }
        }

        ans as i32
    }
}

}
