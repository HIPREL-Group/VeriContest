use vstd::prelude::*;

verus! {

pub proof fn xor_identity(x: i32)
    ensures 0 ^ x == x, x ^ 0 == x
{
    assert(0 ^ x == x) by(bit_vector);
    assert(x ^ 0 == x) by(bit_vector);
}

pub proof fn xor_self_cancel(x: i32)
    ensures x ^ x == 0
{
    assert(x ^ x == 0) by(bit_vector);
}

pub proof fn xor_commutative(a: i32, b: i32)
    ensures a ^ b == b ^ a
{
    assert(a ^ b == b ^ a) by(bit_vector);
}

pub proof fn xor_associative(a: i32, b: i32, c: i32)
    ensures (a ^ b) ^ c == a ^ (b ^ c)
{
    assert((a ^ b) ^ c == a ^ (b ^ c)) by(bit_vector);
}

pub proof fn xor_four_rearrange(a: i32, b: i32, c: i32, d: i32)
    ensures
        (a ^ b) ^ (c ^ d) == (a ^ c) ^ (b ^ d),
{
    assert((a ^ b) ^ (c ^ d) == (a ^ c) ^ (b ^ d)) by(bit_vector);
}

pub proof fn lemma_xor_nonneg(a: i32, b: i32)
    requires
        0 <= a <= i32::MAX,
        0 <= b <= i32::MAX,
    ensures
        (a ^ b) >= 0,
{
    assert(a ^ b >= 0) by(bit_vector)
        requires
            0 <= a <= i32::MAX,
            0 <= b <= i32::MAX;
}

} // verus!
