use vstd::arithmetic::div_mod::lemma_small_mod;
use vstd::arithmetic::power2::{lemma2_to64, pow2};
use vstd::bits::{lemma_low_bits_mask_values, lemma_u32_low_bits_mask_is_mod, low_bits_mask};
use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn is_co_growing(x: Seq<u32>, y: Seq<u32>, n: usize) -> bool {
    x.len() == n && y.len() == n &&
    forall|i: int| 0 <= i && i < n as int - 1 ==>
        #[trigger] x[i] == x[i] &&
        (x[i] ^ y[i]) & (x[i + 1] ^ y[i + 1]) == (x[i] ^ y[i])
}

pub open spec fn lex_le_u32(a: Seq<u32>, b: Seq<u32>) -> bool {
    a.len() == b.len() && (
        a =~= b || exists|p: int|
            0 <= p < a.len()
            && a[p] < b[p]
            && forall|k: int| 0 <= k < p ==> a[k] == b[k]
    )
}

pub open spec fn y_valid(x: Seq<u32>, y: Seq<u32>, n: usize) -> bool {
    y.len() == n
    && (forall|i: int| 0 <= i < n as int ==> (y[i] as int) < 1073741824)
    && is_co_growing(x, y, n)
}

pub open spec fn prefix_or(x: Seq<u32>, len: int) -> u32
    recommends 0 <= len <= x.len()
    decreases len
{
    if len <= 0 {
        0u32
    } else {
        prefix_or(x, len - 1) | x[len - 1]
    }
}

proof fn lemma_bv_init(a: u32)
    ensures a ^ (a ^ a) == a
{
    assert(a ^ (a ^ a) == a) by (bit_vector);
}

proof fn lemma_bv_and_or(a: u32, b: u32)
    ensures a & (a | b) == a,
{
    assert(a & (a | b) == a) by (bit_vector);
}

proof fn lemma_bv_xor_or_xor(z: u32, xi: u32)
    ensures xi ^ ((z | xi) ^ xi) == z | xi,
{
    assert(xi ^ ((z | xi) ^ xi) == z | xi) by (bit_vector);
}

proof fn lemma_bv_xor_cancel(a: u32, b: u32)
    ensures a ^ (a ^ b) == b,
{
    assert(a ^ (a ^ b) == b) by (bit_vector);
}

proof fn lemma_bv_xor_cancel_rev(a: u32, b: u32)
    ensures a ^ (b ^ a) == b,
{
    assert(a ^ (b ^ a) == b) by (bit_vector);
}

proof fn lemma_bv_or_le_max30(a: u32, b: u32)
    requires
        (a as int) < 1073741824int,
        (b as int) < 1073741824int,
    ensures
        ((a | b) as int) < 1073741824int,
{
    lemma_bv_u30_to_mask(a);
    lemma_bv_u30_to_mask(b);
    assert(((a | b) & 0x3FFFFFFFu32) == (a | b)) by (bit_vector)
        requires
            a & 0x3FFFFFFFu32 == a,
            b & 0x3FFFFFFFu32 == b,
    ;
    lemma_bv_mask_to_u30(a | b);
}

proof fn lemma_bv_and_le_right(a: u32, b: u32)
    ensures
        (a & b) <= b,
{
    assert((a & b) <= b) by (bit_vector);
}

proof fn lemma_bv_and_le_left(a: u32, b: u32)
    ensures
        (a & b) <= a,
{
    assert((a & b) <= a) by (bit_vector);
}

proof fn lemma_bv_xor_le_max30(a: u32, b: u32)
    requires
        (a as int) < 1073741824int,
        (b as int) < 1073741824int,
    ensures
        ((a ^ b) as int) < 1073741824int,
{
    lemma_bv_u30_to_mask(a);
    lemma_bv_u30_to_mask(b);
    assert(((a ^ b) & 0x3FFFFFFFu32) == (a ^ b)) by (bit_vector)
        requires
            a & 0x3FFFFFFFu32 == a,
            b & 0x3FFFFFFFu32 == b,
    ;
    lemma_bv_mask_to_u30(a ^ b);
}

proof fn lemma_bv_xor_self_zero(a: u32)
    ensures
        a ^ a == 0u32,
{
    assert(a ^ a == 0u32) by (bit_vector);
}

proof fn lemma_bv_zero_or(a: u32)
    ensures
        0u32 | a == a,
{
    assert(0u32 | a == a) by (bit_vector);
}

proof fn lemma_bv_u30_to_mask(a: u32)
    requires
        (a as int) < 1073741824int,
    ensures
        a & 0x3FFFFFFFu32 == a,
{
    lemma_low_bits_mask_values();
    lemma2_to64();
    lemma_u32_low_bits_mask_is_mod(a, 30);
    lemma_small_mod(a as nat, pow2(30) as nat);
    assert(low_bits_mask(30) == 0x3FFFFFFF);
    assert(pow2(30) == 0x40000000);
    assert(a % 0x40000000u32 == a);
    assert((a & (low_bits_mask(30) as u32)) == a % (pow2(30) as u32));
    assert(a & 0x3FFFFFFFu32 == a);
}

proof fn lemma_bv_mask_to_u30(a: u32)
    requires
        a & 0x3FFFFFFFu32 == a,
    ensures
        (a as int) < 1073741824int,
{
    lemma_low_bits_mask_values();
    lemma2_to64();
    lemma_u32_low_bits_mask_is_mod(a, 30);
    assert(low_bits_mask(30) == 0x3FFFFFFF);
    assert(pow2(30) == 0x40000000);
    assert((a & (low_bits_mask(30) as u32)) == a % (pow2(30) as u32));
    assert(a % 0x40000000u32 == a);
    lemma_small_mod((a % 0x40000000u32) as nat, 0x40000000nat);
    assert((a % 0x40000000u32) < 0x40000000u32);
    assert(a < 0x40000000u32);
    assert((a as int) < 1073741824int);
}

proof fn lemma_bv_y_is_masked_prev(z: u32, xi: u32)
    ensures
        ((z | xi) ^ xi) == (z & (!xi)),
{
    assert(((z | xi) ^ xi) == (z & (!xi))) by (bit_vector);
}

proof fn lemma_bv_local_shape(z: u32, xi: u32, alt: u32)
    requires
        z & (xi ^ alt) == z,
    ensures
        ((z | xi) ^ xi) == (z & alt),
{
    assert(((z | xi) ^ xi) == (z & alt)) by (bit_vector)
        requires
            z & (xi ^ alt) == z,
    ;
}

proof fn lemma_prefix_or_bound(x: Seq<u32>, len: int)
    requires
        0 <= len <= x.len(),
        forall|j: int| 0 <= j < len ==> x[j] < 1073741824u32,
    ensures
        prefix_or(x, len) < 1073741824u32,
    decreases len,
{
    if len > 0 {
        lemma_prefix_or_bound(x, len - 1);
        lemma_bv_or_le_max30(prefix_or(x, len - 1), x[len - 1]);
    }
}

proof fn lemma_prefix_or_step(x: Seq<u32>, len: int)
    requires
        0 < len <= x.len(),
    ensures
        prefix_or(x, len) == prefix_or(x, len - 1) | x[len - 1],
{
    reveal_with_fuel(prefix_or, 1);
}

proof fn lemma_local_min(z: u32, xi: u32, alt: u32)
    requires
        (z as int) < 1073741824int,
        (xi as int) < 1073741824int,
        z & (xi ^ alt) == z,
    ensures
        (((z | xi) ^ xi) as int) < 1073741824int,
        ((z | xi) ^ xi) <= alt,
{
    lemma_bv_local_shape(z, xi, alt);
    lemma_bv_u30_to_mask(z);
    assert((((z | xi) ^ xi) & 0x3FFFFFFFu32) == ((z | xi) ^ xi)) by (bit_vector)
        requires
            ((z | xi) ^ xi) == (z & alt),
            z & 0x3FFFFFFFu32 == z,
    ;
    lemma_bv_mask_to_u30((z | xi) ^ xi);
    lemma_bv_and_le_right(z, alt);
    assert(((z | xi) ^ xi) <= alt);
}

proof fn lemma_lex_le_u32_witness(a: Seq<u32>, b: Seq<u32>, p: int)
    requires
        a.len() == b.len(),
        0 <= p < a.len(),
        a[p] < b[p],
        forall|k: int| 0 <= k < p ==> a[k] == b[k],
    ensures
        lex_le_u32(a, b),
{
    assert(exists|w: int|
        0 <= w < a.len()
        && a[w] < b[w]
        && forall|k: int| 0 <= k < w ==> a[k] == b[k]
    ) by {
        assert(0 <= p < a.len());
        assert(a[p] < b[p]);
        assert(forall|k: int| 0 <= k < p ==> a[k] == b[k]);
    }
}

#[verifier::spinoff_prover]
proof fn lemma_minimality(
    x: Seq<u32>,
    y: Seq<u32>,
    alt: Seq<u32>,
    n: usize,
    p: int,
)
    requires
        x.len() == n,
        y.len() == n,
        alt.len() == n,
        y_valid(x, y, n),
        y_valid(x, alt, n),
        y[0] == 0u32,
        forall|j: int| 0 <= j < n as int ==> x[j] < 1073741824u32,
        forall|j: int| 0 < j < n as int ==> #[trigger] y[j] == ((x[j - 1] ^ y[j - 1]) | x[j]) ^ x[j],
        0 <= p <= n as int,
        forall|k: int| 0 <= k < p ==> y[k] == alt[k],
    ensures
        lex_le_u32(y, alt),
    decreases n as int - p,
{
    if p == n as int {
        assert(forall|k: int| 0 <= k < n as int ==> y[k] == alt[k]);
        assert(y =~= alt);
    } else if y[p] < alt[p] {
        lemma_lex_le_u32_witness(y, alt, p);
    } else if y[p] == alt[p] {
        lemma_minimality(x, y, alt, n, p + 1);
    } else {
        assert(alt[p] < y[p]);
        if p == 0 {
            assert(y[0] == 0u32);
            assert(0u32 <= alt[0]);
            assert(false);
        } else {
            lemma_bv_xor_le_max30(x[p - 1], y[p - 1]);
            assert(x[p] < 1073741824u32);
            assert(y[p - 1] == alt[p - 1]);
            assert(x[p - 1] ^ alt[p - 1] == x[p - 1] ^ y[p - 1]);
            assert((x[p - 1] ^ alt[p - 1]) & (x[p] ^ alt[p]) == (x[p - 1] ^ alt[p - 1]));
            assert((x[p - 1] ^ y[p - 1]) & (x[p] ^ alt[p]) == (x[p - 1] ^ y[p - 1]));
            lemma_local_min(x[p - 1] ^ y[p - 1], x[p], alt[p]);
            assert(y[p] == ((x[p - 1] ^ y[p - 1]) | x[p]) ^ x[p]);
            assert(y[p] <= alt[p]);
            assert(false);
        }
    }
}

pub struct Solution;

impl Solution {
    #[verifier::spinoff_prover]
    pub fn co_growing(n: usize, x: Vec<u32>) -> (y: Vec<u32>)
        requires
            1 <= n && n <= 200000,
            x.len() == n,
            forall|i: int| 0 <= i && i < n ==> x@[i] < 1073741824,
        ensures
            y.len() == n,
            y_valid(x@, y@, n),
            forall|alt: Seq<u32>| y_valid(x@, alt, n) ==> lex_le_u32(y@, alt),
    {
        let mut y: Vec<u32> = Vec::new();
        let mut z: u32 = x[0];
        let y0 = z ^ x[0];
        proof {
            lemma_bv_init(z);
            assert(y0 == x[0] ^ x[0]);
            lemma_bv_xor_self_zero(x[0]);
            assert(y0 == 0u32);
        }
        y.push(y0);
        proof {
            assert(y@[0] == y0);
            assert(y@[0] == 0u32);
            assert(y@[0] < 1073741824u32);
            assert(x@[0] ^ y@[0] == z);
        }
        let mut i: usize = 1;
        while i < n
            invariant
                1 <= i && i <= n,
                n <= 200000,
                x.len() == n,
                y.len() == i,
                forall|j: int| 0 <= j && j < n ==> x@[j] < 1073741824,
                (z as int) < 1073741824int,
                y@[0] == 0u32,
                forall|j: int| 0 <= j < i as int ==> y@[j] < 1073741824u32,
                x@[i as int - 1] ^ y@[i as int - 1] == z,
                forall|j: int| 0 < j < i as int ==> #[trigger] y@[j] == ((x@[j - 1] ^ y@[j - 1]) | x@[j]) ^ x@[j],
                forall|j: int| #![trigger x@[j]] 0 <= j && j < i as int - 1 ==>
                    (x@[j] ^ y@[j]) & (x@[j + 1] ^ y@[j + 1]) == (x@[j] ^ y@[j]),
            decreases n - i
        {
            let xi = x[i];
            let old_z = z;
            z = z | x[i];
            let yi = z ^ x[i];
            proof {
                lemma_bv_or_le_max30(old_z, x@[i as int]);
                assert(xi == x@[i as int]);
                assert(z == old_z | xi);
                assert(yi == z ^ xi);
                lemma_bv_xor_or_xor(old_z, x@[i as int]);
                assert((z as int) < 1073741824int);
                lemma_bv_y_is_masked_prev(old_z, xi);
                assert(yi == old_z & (!xi));
                lemma_bv_u30_to_mask(old_z);
                assert((yi & 0x3FFFFFFFu32) == yi) by (bit_vector)
                    requires
                        yi == old_z & (!xi),
                        old_z & 0x3FFFFFFFu32 == old_z,
                ;
                lemma_bv_mask_to_u30(yi);
                assert(yi < 1073741824u32);
            }
            y.push(yi);
            proof {
                assert(y@[i as int] == yi);
                assert forall|j: int| 0 <= j < i as int + 1 implies y@[j] < 1073741824u32 by {
                    if j < i as int {
                    } else {
                        assert(j == i as int);
                        assert(y@[j] == yi);
                    }
                }
                assert(x@[i as int] ^ y@[i as int] == z);
                assert forall|j: int| 0 < j < i as int + 1 implies #[trigger] y@[j] == ((x@[j - 1] ^ y@[j - 1]) | x@[j]) ^ x@[j] by {
                    if j < i as int {
                    } else {
                        assert(j == i as int);
                        assert(y@[j] == yi);
                        assert(x@[j - 1] ^ y@[j - 1] == old_z);
                    }
                }
                assert forall|j: int| #![trigger x@[j]] 0 <= j && j < i as int ==>
                    (x@[j] ^ y@[j]) & (x@[j + 1] ^ y@[j + 1]) == (x@[j] ^ y@[j]) by {
                    if 0 <= j && j < i as int {
                        if j < i as int - 1 {
                        } else {
                            assert(i as int - 1 <= j);
                            assert(j < i as int);
                            assert(j == i as int - 1);
                            assert(x@[j] ^ y@[j] == old_z);
                            assert(x@[j + 1] ^ y@[j + 1] == z);
                            lemma_bv_and_or(old_z, x@[i as int]);
                        }
                    }
                }
            }
            i += 1;
        }
        proof {
            assert(i == n);
            assert(y.len() == n);
            assert(y_valid(x@, y@, n));
            assert forall|alt: Seq<u32>| y_valid(x@, alt, n) implies lex_le_u32(y@, alt) by {
                lemma_minimality(x@, y@, alt, n, 0);
            }
        }
        y
    }
}

}
