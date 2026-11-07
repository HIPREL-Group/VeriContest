use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_jump_delta(a: int, b: int, j: int) -> int {
    if j % 2 == 1 {
        a
    } else {
        -b
    }
}

pub open spec fn spec_frog_after_jumps(a: int, b: int, k: int) -> int
    recommends
        k >= 0,
    decreases k,
{
    if k <= 0 {
        0int
    } else {
        spec_frog_after_jumps(a, b, k - 1) + spec_jump_delta(a, b, k)
    }
}

use vstd::arithmetic::div_mod::{lemma_div_by_multiple, lemma_div_of0, lemma_fundamental_div_mod};
use vstd::arithmetic::mul::{lemma_mul_is_distributive_add_other_way, lemma_mul_upper_bound};

proof fn lemma_i64_half_matches_int(k: i64)
    requires
        1 <= k <= 1_000_000_000,
    ensures
        (((k + 1) / 2) as int) == (k as int + 1) / 2,
        ((k / 2) as int) == (k as int) / 2,
{
}

proof fn lemma_frog_product_fits_i64(na: i64, nb: i64, a: i64, b: i64)
    requires
        1 <= a <= 1_000_000_000,
        1 <= b <= 1_000_000_000,
        0 <= na <= 500_000_000,
        0 <= nb <= 500_000_000,
    ensures
        na * a <= i64::MAX,
        nb * b <= i64::MAX,
        na * a - nb * b >= i64::MIN,
        na * a - nb * b <= i64::MAX,
{
    lemma_mul_upper_bound(na as int, 500_000_000, a as int, 1_000_000_000);
    lemma_mul_upper_bound(nb as int, 500_000_000, b as int, 1_000_000_000);
    assert((500_000_000 * 1_000_000_000) == 500_000_000_000_000_000);
    assert(500_000_000_000_000_000 < i64::MAX);
    assert((na as int) * (a as int) <= 500_000_000_000_000_000);
    assert((nb as int) * (b as int) <= 500_000_000_000_000_000);
    assert((na * a) as int == (na as int) * (a as int));
    assert((nb * b) as int == (nb as int) * (b as int));
    assert(-500_000_000_000_000_000 <= (na as int) * (a as int) - (nb as int) * (b as int));
    assert((na as int) * (a as int) - (nb as int) * (b as int) <= 500_000_000_000_000_000);
    assert(-500_000_000_000_000_000 > i64::MIN as int);
    assert(500_000_000_000_000_000 < i64::MAX as int);
}

proof fn lemma_frog_closed_matches_recursive(a: int, b: int, k: int)
    requires
        k >= 0,
    ensures
        spec_frog_after_jumps(a, b, k) == ((k + 1) / 2) * a - (k / 2) * b,
    decreases k,
{
    reveal_with_fuel(spec_frog_after_jumps, 3);
    if k <= 0 {
        assert(spec_frog_after_jumps(a, b, k) == 0);
        lemma_div_of0(2);
        assert((0int + 1) / 2 == 0);
        assert((0int / 2) == 0);
        assert(((k + 1) / 2) * a - (k / 2) * b == 0);
    } else {
        lemma_frog_closed_matches_recursive(a, b, k - 1);
        assert(spec_frog_after_jumps(a, b, k) == spec_frog_after_jumps(a, b, k - 1) + spec_jump_delta(a, b, k));
        assert(spec_frog_after_jumps(a, b, k - 1) == (k / 2) * a - ((k - 1) / 2) * b);
        lemma_fundamental_div_mod(k, 2);
        assert(0 < 2);
        assert(k == 2 * (k / 2) + k % 2);
        let ghost m = k / 2;
        if k % 2 == 1 {
            assert(spec_jump_delta(a, b, k) == a);
            assert(k == 2 * m + 1);
            assert(k + 1 == 2 * (m + 1));
            lemma_div_by_multiple(m + 1, 2);
            assert((k + 1) / 2 == m + 1);
            assert(k - 1 == 2 * m);
            lemma_div_by_multiple(m, 2);
            assert((k - 1) / 2 == m);
            assert(k / 2 == m);
            lemma_mul_is_distributive_add_other_way(a, m, 1);
            assert((m + 1) * a == m * a + a);
            assert(m * a - m * b + a == (m + 1) * a - m * b);
            assert((k / 2) * a - ((k - 1) / 2) * b + a == ((k + 1) / 2) * a - (k / 2) * b);
        } else {
            assert(spec_jump_delta(a, b, k) == -b);
            assert(k == 2 * m);
            assert(m >= 1);
            assert(k + 1 == 2 * m + 1);
            lemma_fundamental_div_mod(2 * m + 1, 2);
            assert((2 * m + 1) / 2 == m);
            assert((k + 1) / 2 == m);
            assert(k - 1 == 2 * m - 1);
            assert(k - 1 == 2 * (m - 1) + 1);
            lemma_fundamental_div_mod(k - 1, 2);
            assert((k - 1) / 2 == m - 1);
            assert(k / 2 == m);
            lemma_mul_is_distributive_add_other_way(b, m - 1, 1);
            assert(m * b == (m - 1) * b + b);
            assert(m * a - (m - 1) * b - b == m * a - m * b);
            assert((k / 2) * a - ((k - 1) / 2) * b - b == ((k + 1) / 2) * a - (k / 2) * b);
        }
        assert(spec_frog_after_jumps(a, b, k) == ((k + 1) / 2) * a - (k / 2) * b);
    }
}

impl Solution {
    pub fn frog_position_after_jumps(a: i64, b: i64, k: i64) -> (result: i64)
        requires
            1 <= a <= 1_000_000_000,
            1 <= b <= 1_000_000_000,
            1 <= k <= 1_000_000_000,
        ensures
            result as int == spec_frog_after_jumps(a as int, b as int, k as int),
            exists|na: int, nb: int|
                na == (k as int + 1) / 2 && nb == (k as int) / 2 && na + nb == k as int && result as int == #[trigger] (na * (a as int) - nb * (b as int)),
    {
        proof {
            lemma_frog_closed_matches_recursive(a as int, b as int, k as int);
            lemma_i64_half_matches_int(k);
        }
        let na = (k + 1) / 2;
        let nb = k / 2;
        proof {
            assert(0 <= na <= 500_000_000);
            assert(0 <= nb <= 500_000_000);
            lemma_frog_product_fits_i64(na, nb, a, b);
            assert((na as int) == (k as int + 1) / 2);
            assert((nb as int) == (k as int) / 2);
            assert((na as int) + (nb as int) == k as int);
            assert(((na * a - nb * b) as int) == (na as int) * (a as int) - (nb as int) * (b as int));
            assert((na * a - nb * b) as int == spec_frog_after_jumps(a as int, b as int, k as int));
        }
        na * a - nb * b
    }
}

}
