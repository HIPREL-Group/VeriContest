use vstd::arithmetic::div_mod::{
    lemma_div_is_ordered, lemma_fundamental_div_mod, lemma_mul_mod_noop,
    lemma_mul_mod_noop_right, lemma_small_mod,
};
use vstd::arithmetic::mul::lemma_mul_inequality;
use vstd::arithmetic::power::{
    lemma_pow0, lemma_pow1, lemma_pow_adds, lemma_pow_multiplies, lemma_pow_positive,
    lemma_square_is_pow2, pow,
};
use vstd::arithmetic::power2::{
    lemma2_to64, lemma2_to64_rest, lemma_pow2_pos, lemma_pow2_unfold, pow2,
};
use vstd::bits::{
    lemma_u64_low_bits_mask_is_mod, lemma_u64_shl_is_mul, lemma_u64_shr_is_div,
};
use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

proof fn lemma_mul_is_zero(x: int, y: int)
    by (nonlinear_arith)
    requires
        x * y == 0,
    ensures
        x == 0 || y == 0,
{
}

proof fn lemma_div_is_zero(x: int, d: int)
    requires
        d > 0,
    ensures
        0 <= x < d <==> x / d == 0,
{
    lemma_fundamental_div_mod(x, d);
    if 0 <= x < d {
        lemma_small_mod(x as nat, d as nat);
        lemma_mul_is_zero(d, x / d);
    }
}



pub open spec fn cfp(n: int) -> int {
    if n <= 0 { 1 }
    else if n <= 3 { n }
    else if n % 3 == 0 { pow(3, (n / 3) as nat) }
    else if n % 3 == 1 { 4 * pow(3, ((n - 4) / 3) as nat) }
    else { 2 * pow(3, ((n - 2) / 3) as nat) }
}

proof fn lemma_cfp_positive(n: int)
    requires n >= 0,
    ensures cfp(n) > 0,
{
    if n >= 1 { lemma_cfp_ge_n(n); }
}

proof fn lemma_cfp_ge_n(n: int)
    requires n >= 1,
    ensures cfp(n) >= n,
    decreases n,
{
    if n <= 3 {
    } else if n == 4 {
        lemma_pow0(3int);
    } else {
        lemma_cfp_recurrence(n);
        lemma_cfp_ge_n(n - 3);
        assert(3 * (n - 3) >= n) by (nonlinear_arith) requires n >= 5;
    }
}

proof fn lemma_cfp_recurrence(n: int)
    requires n >= 5,
    ensures cfp(n) == 3 * cfp(n - 3),
{
    let m = n - 3;
    if n % 3 == 0 {
        assert(m % 3 == 0);
        if m <= 3 {
            assert(cfp(3) == 3);
            lemma_pow1(3int);
            assert(n / 3 == 2) by (nonlinear_arith) requires n % 3 == 0, n - 3 <= 3, n >= 5;
            lemma_pow_adds(3, 1, 1);
            lemma_pow1(3int);
        } else {
            assert((n / 3) as nat == ((m / 3) + 1) as nat) by (nonlinear_arith)
                requires n % 3 == 0, m == n - 3;
            lemma_pow_adds(3, (m / 3) as nat, 1);
            lemma_pow1(3int);
        }
    } else if n % 3 == 1 {
        assert(m % 3 == 1) by (nonlinear_arith) requires n % 3 == 1, m == n - 3;
        assert(m >= 4) by (nonlinear_arith) requires m % 3 == 1, m >= 2;
        assert(((n - 4) / 3) as nat == (((m - 4) / 3) + 1) as nat) by (nonlinear_arith)
            requires n % 3 == 1, m == n - 3, m >= 4;
        lemma_pow_adds(3, ((m - 4) / 3) as nat, 1);
        lemma_pow1(3int);
    } else {
        assert(m % 3 == 2) by (nonlinear_arith) requires n % 3 == 2, m == n - 3;
        if m <= 3 {
            assert(m == 2) by (nonlinear_arith) requires m % 3 == 2, m >= 2, m <= 3;
            assert(cfp(m) == 2);
            assert((n - 2) / 3 == 1) by (nonlinear_arith) requires n == 5;
            lemma_pow1(3int);
        } else {
            assert(((n - 2) / 3) as nat == (((m - 2) / 3) + 1) as nat) by (nonlinear_arith)
                requires n % 3 == 2, m == n - 3, m >= 4;
            lemma_pow_adds(3, ((m - 2) / 3) as nat, 1);
            lemma_pow1(3int);
        }
    }
}

proof fn lemma_cfp_monotone(n: int)
    requires n >= 1,
    ensures cfp(n) <= cfp(n + 1),
    decreases n,
{
    if n <= 2 {
    } else if n == 3 {
        lemma_pow0(3int);
    } else if n == 4 {
        lemma_pow0(3int);
        assert(cfp(5) == 2 * pow(3, 1));
        lemma_pow1(3int);
    } else {
        lemma_cfp_recurrence(n);
        lemma_cfp_recurrence(n + 1);
        lemma_cfp_monotone(n - 3);
    }
}

proof fn lemma_2cfp_bound(n: int)
    requires n >= 4,
    ensures 2 * cfp(n - 2) <= cfp(n),
    decreases n,
{
    if n == 4 {
        lemma_pow0(3int);
    } else if n == 5 {
        assert(cfp(5) == 2 * pow(3, 1)); lemma_pow1(3int);
    } else if n == 6 {
        lemma_pow0(3int);
        assert(cfp(6) == pow(3, 2));
        lemma_pow_adds(3, 1, 1); lemma_pow1(3int);
    } else if n == 7 {
        assert(cfp(5) == 2 * pow(3, 1)); lemma_pow1(3int);
        assert(cfp(7) == 4 * pow(3, 1)); lemma_pow1(3int);
    } else {
        lemma_cfp_recurrence(n);
        lemma_cfp_recurrence(n - 2);
        lemma_2cfp_bound(n - 3);
    }
}

proof fn lemma_k_cfp_bound(n: int, k: int)
    requires n >= 4, 1 <= k <= n - 1,
    ensures k * cfp(n - k) <= cfp(n),
    decreases n, n - k,
{
    if n <= 7 {
        lemma_cfp_base_values();
        if n == 4 {
            assert(k * cfp(n - k) <= 4) by (nonlinear_arith)
                requires 1 <= k <= 3, cfp(1) == 1, cfp(2) == 2, cfp(3) == 3,
                    cfp(n - k) == (if k == 1 { 3int } else if k == 2 { 2int } else { 1int });
        } else if n == 5 {
            assert(cfp(5) == 6);
            if k == 1 { assert(cfp(4) == 4); }
            else if k == 2 { assert(cfp(3) == 3); }
            else if k == 3 { assert(cfp(2) == 2); }
            else { assert(cfp(1) == 1); }
        } else if n == 6 {
            assert(cfp(6) == 9);
            if k == 1 { assert(cfp(5) == 6); }
            else if k == 2 { assert(cfp(4) == 4); }
            else if k == 3 { assert(cfp(3) == 3); }
            else if k == 4 { assert(cfp(2) == 2); }
            else { assert(cfp(1) == 1); }
        } else {
            assert(cfp(7) == 12);
            if k == 1 { assert(cfp(6) == 9); }
            else if k == 2 { assert(cfp(5) == 6); }
            else if k == 3 { assert(cfp(4) == 4); }
            else if k == 4 { assert(cfp(3) == 3); }
            else if k == 5 { assert(cfp(2) == 2); }
            else { assert(cfp(1) == 1); }
        }
    } else {
        lemma_cfp_recurrence(n);
        if k == 1 {
            lemma_cfp_monotone(n - 1);
        } else if k == 2 {
            lemma_2cfp_bound(n);
        } else if k == 3 {
            
        } else if k == 4 {
            lemma_2cfp_bound(n - 2);
            lemma_2cfp_bound(n);
            lemma_cfp_positive(n - 4);
        } else {
            
            assert(k <= 3 * (k - 3)) by (nonlinear_arith) requires k >= 5;
            assert(n - 3 >= 4 && 1 <= k - 3 <= (n - 3) - 1) by (nonlinear_arith)
                requires n >= 8, k >= 5, k <= n - 1;
            lemma_k_cfp_bound(n - 3, k - 3);
            lemma_cfp_positive(n - k);
            assert(k * cfp(n - k) <= 3 * (k - 3) * cfp(n - k)) by (nonlinear_arith)
                requires k <= 3 * (k - 3), cfp(n - k) >= 0;
            assert(3 * (k - 3) * cfp(n - k) <= 3 * cfp(n - 3)) by (nonlinear_arith)
                requires (k - 3) * cfp(n - k) <= cfp(n - 3);
        }
    }
}

proof fn lemma_cfp_base_values()
    ensures
        cfp(1) == 1, cfp(2) == 2, cfp(3) == 3, cfp(4) == 4,
        cfp(5) == 6, cfp(6) == 9, cfp(7) == 12,
{
    lemma_pow1(3int);
    lemma_pow_adds(3, 1, 1);
    lemma_pow0(3int);
    assert(cfp(5) == 2 * pow(3, 1));
    assert(cfp(6) == pow(3, 2));
    assert(cfp(7) == 4 * pow(3, 1));
}



proof fn lemma_partition_sum_prefix(a: Seq<int>, b: Seq<int>, hi: nat)
    requires
        hi <= a.len(), hi <= b.len(),
        forall |i: int| 0 <= i < hi ==> a[i] == b[i],
    ensures
        Solution::partition_sum(a, hi as int) == Solution::partition_sum(b, hi as int),
    decreases hi,
{
    if hi > 0 { lemma_partition_sum_prefix(a, b, (hi - 1) as nat); }
}

proof fn lemma_partition_product_prefix(a: Seq<int>, b: Seq<int>, hi: nat)
    requires
        hi <= a.len(), hi <= b.len(),
        forall |i: int| 0 <= i < hi ==> a[i] == b[i],
    ensures
        Solution::partition_product(a, hi as int) == Solution::partition_product(b, hi as int),
    decreases hi,
{
    if hi > 0 { lemma_partition_product_prefix(a, b, (hi - 1) as nat); }
}

proof fn lemma_const_seq_sum(val: int, len: nat)
    ensures Solution::partition_sum(Seq::new(len, |_i: int| val), len as int) == val * len,
    decreases len,
{
    let s = Seq::new(len, |_i: int| val);
    if len == 0 {
    } else {
        lemma_const_seq_sum(val, (len - 1) as nat);
        let s2 = Seq::new((len - 1) as nat, |_i: int| val);
        assert forall |i: int| 0 <= i < (len - 1) as int implies s[i] == s2[i] by {}
        lemma_partition_sum_prefix(s, s2, (len - 1) as nat);
        assert(s[len as int - 1] == val);
        
        assert(val * ((len - 1) as int) + val == val * (len as int)) by (nonlinear_arith);
    }
}

proof fn lemma_const_seq_product(val: int, len: nat)
    ensures Solution::partition_product(Seq::new(len, |_i: int| val), len as int) == pow(val, len),
    decreases len,
{
    let s = Seq::new(len, |_i: int| val);
    if len == 0 {
        lemma_pow0(val);
    } else {
        lemma_const_seq_product(val, (len - 1) as nat);
        let s2 = Seq::new((len - 1) as nat, |_i: int| val);
        assert forall |i: int| 0 <= i < (len - 1) as int implies s[i] == s2[i] by {}
        lemma_partition_product_prefix(s, s2, (len - 1) as nat);
        assert(s[len as int - 1] == val);
        lemma_pow_adds(val, (len - 1) as nat, 1);
        lemma_pow1(val);
    }
}

proof fn lemma_partition_sum_concat(a: Seq<int>, b: Seq<int>)
    ensures
        Solution::partition_sum(a + b, (a.len() + b.len()) as int)
            == Solution::partition_sum(a, a.len() as int)
             + Solution::partition_sum(b, b.len() as int),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
    } else {
        let bp = b.subrange(0, b.len() as int - 1);
        lemma_partition_sum_concat(a, bp);
        let ab = a + b;
        let abp = a + bp;
        assert(ab.subrange(0, (a.len() + b.len() - 1) as int) =~= abp);
        lemma_partition_sum_prefix(ab, abp, (a.len() + b.len() - 1) as nat);
        assert(ab[(a.len() + b.len() - 1) as int] == b[b.len() as int - 1]);
        lemma_partition_sum_prefix(b, bp, (b.len() - 1) as nat);
    }
}

proof fn lemma_partition_product_concat(a: Seq<int>, b: Seq<int>)
    ensures
        Solution::partition_product(a + b, (a.len() + b.len()) as int)
            == Solution::partition_product(a, a.len() as int)
             * Solution::partition_product(b, b.len() as int),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
    } else {
        let bp = b.subrange(0, b.len() as int - 1);
        lemma_partition_product_concat(a, bp);
        let ab = a + b;
        let abp = a + bp;
        let total = (a.len() + b.len()) as int;
        let pp_a = Solution::partition_product(a, a.len() as int);
        let pp_bp = Solution::partition_product(bp, bp.len() as int);
        assert(ab.subrange(0, total - 1) =~= abp);
        lemma_partition_product_prefix(ab, abp, (a.len() + b.len() - 1) as nat);
        
        assert(ab[total - 1] == b[b.len() as int - 1]);
        lemma_partition_product_prefix(b, bp, (b.len() - 1) as nat);
        
        let pp_b_tail = b[b.len() as int - 1];
        
        
        assert(pp_a * pp_bp * pp_b_tail == pp_a * (pp_bp * pp_b_tail)) by (nonlinear_arith);
    }
}

proof fn lemma_partition_split_first(parts: Seq<int>)
    requires parts.len() >= 1,
    ensures ({
        let rest = parts.subrange(1, parts.len() as int);
        &&& Solution::partition_sum(parts, parts.len() as int)
            == parts[0] + Solution::partition_sum(rest, rest.len() as int)
        &&& Solution::partition_product(parts, parts.len() as int)
            == parts[0] * Solution::partition_product(rest, rest.len() as int)
    }),
{
    let first: Seq<int> = seq![parts[0]];
    let rest = parts.subrange(1, parts.len() as int);
    assert(first + rest =~= parts);
    lemma_partition_sum_concat(first, rest);
    lemma_partition_product_concat(first, rest);
    assert(Solution::partition_sum(first, 1) == parts[0]) by {
        assert(Solution::partition_sum(first, 0) == 0);
    }
    assert(Solution::partition_product(first, 1) == parts[0]) by {
        assert(Solution::partition_product(first, 0) == 1);
    }
}

proof fn lemma_partition_sum_lower_bound(parts: Seq<int>, hi: int)
    requires
        hi >= 0, hi <= parts.len(),
        forall |i: int| 0 <= i < hi ==> parts[i] >= 1,
    ensures
        Solution::partition_sum(parts, hi) >= hi,
    decreases hi,
{
    if hi > 0 { lemma_partition_sum_lower_bound(parts, hi - 1); }
}



proof fn lemma_partition_bound(parts: Seq<int>, n: int)
    requires
        n >= 1, parts.len() > 0,
        forall |i: int| 0 <= i < parts.len() ==> parts[i] >= 1,
        Solution::partition_sum(parts, parts.len() as int) == n,
    ensures
        Solution::partition_product(parts, parts.len() as int) <= cfp(n),
    decreases n,
{
    if parts.len() == 1 {
        assert(Solution::partition_product(parts, 1)
            == Solution::partition_product(parts, 0) * parts[0] == parts[0]);
        assert(Solution::partition_sum(parts, 1)
            == Solution::partition_sum(parts, 0) + parts[0] == parts[0]);
        lemma_cfp_ge_n(n);
    } else {
        lemma_partition_split_first(parts);
        let k = parts[0];
        let rest = parts.subrange(1, parts.len() as int);
        let rest_sum = Solution::partition_sum(rest, rest.len() as int);
        let rest_prod = Solution::partition_product(rest, rest.len() as int);
        
        lemma_partition_sum_lower_bound(rest, rest.len() as int);
        assert(1 <= k && k <= n - 1);
        assert(n - k >= 1);
        lemma_partition_bound(rest, n - k);
        lemma_cfp_positive(n - k);
        assert(k * rest_prod <= k * cfp(n - k)) by (nonlinear_arith)
            requires rest_prod <= cfp(n - k), k >= 1, cfp(n - k) > 0;
        if n >= 4 {
            lemma_k_cfp_bound(n, k);
        } else {
            assert(n >= 2);
            
            
            assert(k * cfp(n - k) <= cfp(n)) by (nonlinear_arith)
                requires
                    n >= 2, n <= 3, k >= 1, k <= n - 1,
                    cfp(1int) == 1, cfp(2int) == 2, cfp(3int) == 3,
                    cfp(n - k) == (if n - k == 1 { 1int } else { 2int }),
                    cfp(n) == n;
        }
        assert(k * cfp(n - k) <= cfp(n));
        assert(Solution::partition_product(parts, parts.len() as int) == k * rest_prod);
    }
}



proof fn lemma_witness_partition(n: int) -> (parts: Seq<int>)
    requires n >= 1,
    ensures
        parts.len() > 0,
        forall |i: int| 0 <= i < parts.len() ==> parts[i] >= 1,
        Solution::partition_sum(parts, parts.len() as int) == n,
        Solution::partition_product(parts, parts.len() as int) == cfp(n),
    decreases n,
{
    if n <= 3 {
        let parts: Seq<int> = seq![n];
        assert(Solution::partition_sum(parts, 1)
            == Solution::partition_sum(parts, 0) + parts[0] == n);
        assert(Solution::partition_product(parts, 1)
            == Solution::partition_product(parts, 0) * parts[0] == n);
        parts
    } else if n % 3 == 0 {
        let k = (n / 3) as nat;
        let parts = Seq::new(k, |_i: int| 3int);
        lemma_const_seq_sum(3, k);
        assert(3int * k == n) by (nonlinear_arith) requires n % 3 == 0, k == (n / 3) as nat, n >= 4;
        lemma_const_seq_product(3, k);
        parts
    } else if n % 3 == 1 {
        let k3 = ((n - 4) / 3) as nat;
        let threes = Seq::new(k3, |_i: int| 3int);
        let twos: Seq<int> = seq![2int, 2int];
        let parts = threes + twos;
        lemma_const_seq_sum(3, k3);
        assert(Solution::partition_sum(twos, 2) == 4) by {
            assert(Solution::partition_sum(twos, 0) == 0);
            assert(Solution::partition_sum(twos, 1) == 0 + twos[0] == 2);
        }
        lemma_partition_sum_concat(threes, twos);
        assert(3int * k3 + 4 == n) by (nonlinear_arith)
            requires n % 3 == 1, k3 == ((n - 4) / 3) as nat, n >= 4;
        lemma_const_seq_product(3, k3);
        assert(Solution::partition_product(twos, 2) == 4) by {
            assert(Solution::partition_product(twos, 0) == 1);
            assert(Solution::partition_product(twos, 1) == 1 * twos[0] == 2);
        }
        lemma_partition_product_concat(threes, twos);
        assert(parts.len() == k3 + 2);
        assert forall |i: int| 0 <= i < parts.len() implies parts[i] >= 1 by {
            if i < k3 as int { assert(parts[i] == threes[i]); }
            else { assert(parts[i] == twos[i - k3 as int]); }
        }
        parts
    } else {
        let k3 = ((n - 2) / 3) as nat;
        let threes = Seq::new(k3, |_i: int| 3int);
        let two: Seq<int> = seq![2int];
        let parts = threes + two;
        lemma_const_seq_sum(3, k3);
        assert(Solution::partition_sum(two, 1) == 2) by {
            assert(Solution::partition_sum(two, 0) == 0);
        }
        lemma_partition_sum_concat(threes, two);
        assert(3int * k3 + 2 == n) by (nonlinear_arith)
            requires n % 3 == 2, k3 == ((n - 2) / 3) as nat, n >= 4;
        lemma_const_seq_product(3, k3);
        assert(Solution::partition_product(two, 1) == 2) by {
            assert(Solution::partition_product(two, 0) == 1);
        }
        lemma_partition_product_concat(threes, two);
        assert(parts.len() == k3 + 1);
        assert forall |i: int| 0 <= i < parts.len() implies parts[i] >= 1 by {
            if i < k3 as int { assert(parts[i] == threes[i]); }
            else { assert(parts[i] == two[i - k3 as int]); }
        }
        parts
    }
}



#[verifier::spinoff_prover]
fn mod_pow(base: u64, exp: u64, modulus: u64) -> u64
    requires
        0 < modulus <= u32::MAX + 1,
    returns
        (pow(base as int, exp as nat) % modulus as int) as u64,
{
    if modulus == 1 {
        return 0;
    }
    let mut result: u64 = 1;
    let mut base_pow = base % modulus;
    let mut i: u64 = 0;
    let mut mut_exp = exp;
    proof {
        assert(mut_exp == exp >> i) by (bit_vector)
            requires
                i == 0,
                mut_exp == exp,
        ;
        lemma_u64_shr_is_div(exp, i);
        lemma2_to64();
        lemma_pow1(base as int);
        lemma_pow0(base as int);
        lemma_small_mod(1, modulus as nat);
    }
    while mut_exp > 0
        invariant
            0 < modulus <= u32::MAX + 1,
            base_pow < modulus,
            0 <= result < modulus,
            i < 64 ==> (mut_exp == exp >> i == exp as nat / pow2(i as nat)),
            i == 64 ==> mut_exp == 0,
            0 <= i <= 64,
            result == pow(base as int, exp as nat % pow2(i as nat)) % modulus as int,
            base_pow == pow(base as int, pow2(i as nat)) % modulus as int,
        decreases mut_exp,
    {
        proof {
            assert(result == pow(base as int, exp as nat % pow2(i as nat)) % modulus as int);
            assert(exp & ((1u64 << i + 1) - 1) as u64 == (exp & (1u64 << i)) + (exp & (((1u64
                << i) - 1) as u64))) by (bit_vector);
            assert((mut_exp & 1) << i == exp & (1u64 << i)) by (bit_vector)
                requires
                    mut_exp == exp >> i,
            ;
            lemma2_to64();
            lemma2_to64_rest();
            if i + 1 <= 63 {
                assert(pow2(i as nat + 1) < u64::MAX);
                lemma_u64_shl_is_mul(1, (i + 1) as u64);
                lemma_u64_low_bits_mask_is_mod(exp, i as nat + 1);
            } else {
                assert(exp & ((1u64 << i + 1) - 1) as u64 == exp) by (bit_vector)
                    requires
                        i + 1 == 64,
                ;
                lemma_small_mod(exp as nat, pow2(64));
            }
            lemma_u64_low_bits_mask_is_mod(mut_exp, 1);
            assert(mut_exp & 1 == mut_exp % 2);
            assert(pow2(i as nat) < u64::MAX);
            assert(mut_exp & 1 <= 1);
            lemma_u64_shl_is_mul(mut_exp & 1, i);
            lemma_u64_shl_is_mul(1, i);
            lemma_u64_low_bits_mask_is_mod(exp, i as nat);
            if mut_exp % 2 == 0 {
            } else {
                lemma_pow_adds(base as int, pow2(i as nat), exp as nat % pow2(i as nat));
                lemma_mul_mod_noop(
                    pow(base as int, exp as nat % pow2(i as nat)),
                    pow(base as int, pow2(i as nat)),
                    modulus as int,
                );
            }
        }
        if mut_exp % 2 != 0 {
            proof {
                lemma_mul_inequality(base_pow as int, u32::MAX as int + 1, result as int);
            }
            result = result * base_pow % modulus;
        }
        proof {
            lemma_mul_inequality(base_pow as int, u32::MAX as int + 1, base_pow as int);
            lemma_u64_shr_is_div(mut_exp, 1);
            lemma_u64_shr_is_div(exp, i);
            if i == 63 {
                assert(u64::MAX >> i == 1) by (bit_vector)
                    requires
                        i == 63,
                ;
                lemma_u64_shr_is_div(u64::MAX, i);
                lemma_pow2_pos(i as nat);
                lemma_div_is_ordered(exp as int, u64::MAX as int, pow2(i as nat) as int);
            } else {
                assert(mut_exp >> 1 == exp >> (i + 1)) by (bit_vector)
                    requires
                        mut_exp == exp >> i,
                ;
                lemma_u64_shr_is_div(exp, (i + 1) as u64);
            }
            lemma_square_is_pow2(base_pow as int);
            lemma_mul_mod_noop(
                pow(base as int, pow2(i as nat)),
                pow(base as int, pow2(i as nat)),
                modulus as int,
            );
            lemma_pow_multiplies(base as int, pow2(i as nat), 2);
            lemma_square_is_pow2(pow(base as int, pow2(i as nat)));
            lemma_pow2_unfold(i as nat + 1);
        }
        base_pow = base_pow * base_pow % modulus;
        mut_exp >>= 1;
        i += 1;
    }
    proof {
        assert(result == pow(base as int, exp as nat % pow2(i as nat)) % modulus as int);
        if i == 64 {
            lemma2_to64();
        } else {
            lemma_pow2_pos(i as nat);
            lemma_div_is_zero(exp as int, pow2(i as nat) as int);
        }
        lemma_small_mod(exp as nat, pow2(i as nat));
    }
    result
}



impl Solution {
    pub open spec fn partition_sum(parts: Seq<int>, hi: int) -> int
        decreases hi,
    {
        if hi <= 0 {
            0
        } else {
            Self::partition_sum(parts, hi - 1) + parts[hi - 1]
        }
    }

    pub open spec fn partition_product(parts: Seq<int>, hi: int) -> int
        decreases hi,
    {
        if hi <= 0 {
            1
        } else {
            Self::partition_product(parts, hi - 1) * parts[hi - 1]
        }
    }

    pub fn max_nice_divisors(prime_factors: i32) -> (res: i32)
        requires
            1 <= prime_factors <= 1_000_000_000,
        ensures
            0 <= res,
            exists |parts: Seq<int>|
                #![trigger Self::partition_product(parts, parts.len() as int)]
                parts.len() > 0
                && (forall |i: int| 0 <= i < parts.len() ==> parts[i] >= 1)
                && Self::partition_sum(parts, parts.len() as int) == prime_factors as int
                && Self::partition_product(parts, parts.len() as int) % 1_000_000_007 == res as int
                && (forall |other: Seq<int>|
                    #![trigger Self::partition_product(other, other.len() as int)]
                    other.len() > 0
                    && (forall |j: int| 0 <= j < other.len() ==> other[j] >= 1)
                    && Self::partition_sum(other, other.len() as int) == prime_factors as int
                    ==> Self::partition_product(other, other.len() as int)
                        <= Self::partition_product(parts, parts.len() as int)),
    {
        let modulus: u64 = 1_000_000_007;
        if prime_factors <= 3 {
            proof {
                let n = prime_factors as int;
                let witness = lemma_witness_partition(n);
                lemma_small_mod(n as nat, 1_000_000_007);
                assert forall |other: Seq<int>|
                    other.len() > 0
                    && (forall |j: int| 0 <= j < other.len() ==> other[j] >= 1)
                    && Self::partition_sum(other, other.len() as int) == n
                implies
                    Self::partition_product(other, other.len() as int)
                        <= Self::partition_product(witness, witness.len() as int)
                by {
                    lemma_partition_bound(other, n);
                }
            }
            return prime_factors;
        }
        let pf = prime_factors as u64;
        let remainder = pf % 3;
        if remainder == 0 {
            let p = mod_pow(3, pf / 3, modulus);
            proof {
                let n = prime_factors as int;
                lemma_pow_positive(3, (pf as int / 3) as nat);
                let witness = lemma_witness_partition(n);
                assert forall |other: Seq<int>|
                    other.len() > 0
                    && (forall |j: int| 0 <= j < other.len() ==> other[j] >= 1)
                    && Self::partition_sum(other, other.len() as int) == n
                implies
                    Self::partition_product(other, other.len() as int)
                        <= Self::partition_product(witness, witness.len() as int)
                by {
                    lemma_partition_bound(other, n);
                }
            }
            p as i32
        } else if remainder == 1 {
            let exp = (pf - 4) / 3;
            let p = mod_pow(3, exp, modulus);
            proof {
                let n = prime_factors as int;
                lemma_pow_positive(3, exp as nat);
                lemma_mul_mod_noop_right(4, pow(3, exp as nat), 1_000_000_007);
                let witness = lemma_witness_partition(n);
                assert forall |other: Seq<int>|
                    other.len() > 0
                    && (forall |j: int| 0 <= j < other.len() ==> other[j] >= 1)
                    && Self::partition_sum(other, other.len() as int) == n
                implies
                    Self::partition_product(other, other.len() as int)
                        <= Self::partition_product(witness, witness.len() as int)
                by {
                    lemma_partition_bound(other, n);
                }
            }
            (4 * p % modulus) as i32
        } else {
            let exp = pf / 3;
            let p = mod_pow(3, exp, modulus);
            proof {
                let n = prime_factors as int;
                lemma_pow_positive(3, exp as nat);
                lemma_mul_mod_noop_right(2, pow(3, exp as nat), 1_000_000_007);
                let witness = lemma_witness_partition(n);
                assert(n / 3 == (n - 2) / 3) by (nonlinear_arith)
                    requires n % 3 == 2;
                assert forall |other: Seq<int>|
                    other.len() > 0
                    && (forall |j: int| 0 <= j < other.len() ==> other[j] >= 1)
                    && Self::partition_sum(other, other.len() as int) == n
                implies
                    Self::partition_product(other, other.len() as int)
                        <= Self::partition_product(witness, witness.len() as int)
                by {
                    lemma_partition_bound(other, n);
                }
            }
            (2 * p % modulus) as i32
        }
    }
}

} 
