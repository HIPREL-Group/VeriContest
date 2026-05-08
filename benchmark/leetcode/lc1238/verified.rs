use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn gray(i: i32) -> i32 {
    i ^ (i >> 1u32)
}

pub open spec fn differs_by_one_bit(a: i32, b: i32) -> bool {
    let d: i32 = a ^ b;
    d > 0i32 && (d & ((d - 1i32) as i32)) == 0i32
}

proof fn lemma_gray_injective(a: i32, b: i32)
    requires
        0 <= a,
        0 <= b,
        a != b,
    ensures
        gray(a) != gray(b),
{
    assert(a ^ (a >> 1u32) != b ^ (b >> 1u32)) by(bit_vector)
        requires a != b, 0 <= a, 0 <= b;
}

proof fn lemma_xor_preserves_neq(a: i32, b: i32, s: i32)
    requires
        a != b,
    ensures
        (s ^ a) != (s ^ b),
{
    assert((s ^ a) != (s ^ b)) by(bit_vector)
        requires a != b;
}

proof fn lemma_gray_adjacent(i: i32)
    requires
        0 <= i,
        i < i32::MAX,
    ensures
        differs_by_one_bit(gray(i), gray((i + 1i32) as i32)),
{
    let next: i32 = (i + 1i32) as i32;
    let g1: i32 = i ^ (i >> 1u32);
    let g2: i32 = next ^ (next >> 1u32);
    let d: i32 = g1 ^ g2;
    let d_minus_1: i32 = (d - 1i32) as i32;
    assert(d > 0i32 && (d & d_minus_1) == 0i32) by(bit_vector)
        requires
            next == (i + 1i32) as i32,
            g1 == i ^ (i >> 1u32),
            g2 == next ^ (next >> 1u32),
            d == g1 ^ g2,
            d_minus_1 == (d - 1i32) as i32,
            0 <= i,
            i < i32::MAX;
}

proof fn lemma_differs_with_xor(a: i32, b: i32, s: i32)
    requires
        differs_by_one_bit(a, b),
    ensures
        differs_by_one_bit(s ^ a, s ^ b),
{
    let d: i32 = a ^ b;
    let d2: i32 = (s ^ a) ^ (s ^ b);
    assert(d2 == d) by(bit_vector)
        requires
            d == a ^ b,
            d2 == (s ^ a) ^ (s ^ b);
}

proof fn lemma_gray_circular(total: i32, n_u: u32)
    requires
        1 <= n_u <= 16,
        total == 1i32 << n_u,
    ensures
        differs_by_one_bit(gray(0i32), gray((total - 1i32) as i32)),
{
    let last: i32 = (total - 1i32) as i32;
    let g0: i32 = 0i32 ^ (0i32 >> 1u32);
    let g_last: i32 = last ^ (last >> 1u32);
    let d: i32 = g0 ^ g_last;
    let d_minus_1: i32 = (d - 1i32) as i32;
    assert(d > 0i32 && (d & d_minus_1) == 0i32) by(bit_vector)
        requires
            last == (total - 1i32) as i32,
            g0 == 0i32 ^ (0i32 >> 1u32),
            g_last == last ^ (last >> 1u32),
            d == g0 ^ g_last,
            d_minus_1 == (d - 1i32) as i32,
            total == 1i32 << n_u,
            1 <= n_u <= 16;
}

proof fn lemma_xor_range(i: i32, start: i32, n_u: u32)
    requires
        1 <= n_u <= 16,
        0 <= i < (1i32 << n_u),
        0 <= start < (1i32 << n_u),
    ensures
        0 <= start ^ (i ^ (i >> 1u32)),
        start ^ (i ^ (i >> 1u32)) < (1i32 << n_u),
{
    assert(0 <= start ^ (i ^ (i >> 1u32)) && start ^ (i ^ (i >> 1u32)) < (1i32 << n_u))
        by(bit_vector)
        requires
            1 <= n_u <= 16,
            0 <= i < (1i32 << n_u),
            0 <= start < (1i32 << n_u);
}

impl Solution {
    pub fn circular_permutation(n: i32, start: i32) -> (result: Vec<i32>)
        requires
            1 <= n <= 16,
            0 <= start < (1i32 << (n as u32)),
        ensures
            result.len() == (1i32 << (n as u32)) as int,
            result[0] == start,
            forall |i: int| 0 <= i < result.len() ==>
                0 <= #[trigger] result[i] < (1i32 << (n as u32)),
            forall |i: int, j: int| 0 <= i < j < result.len() ==>
                result[i] != result[j],
            forall |i: int| 0 <= i < result.len() - 1 ==>
                differs_by_one_bit(#[trigger] result[i], result[i + 1]),
            differs_by_one_bit(result[0], result[result.len() as int - 1]),
    {
        let n_u = n as u32;
        let total = 1i32 << n_u;
        let mut result: Vec<i32> = Vec::new();
        let mut i: i32 = 0;

        while i < total
            invariant
                0 <= i <= total,
                total == (1i32 << n_u),
                1 <= n_u <= 16,
                n_u == n as u32,
                1 <= n <= 16,
                0 <= start < total,
                result.len() == i as int,
                forall |k: int| 0 <= k < i ==>
                    #[trigger] result@[k] == start ^ gray(k as i32),
                forall |k: int| 0 <= k < i ==>
                    0 <= #[trigger] result@[k] < total,
                forall |k: int, m: int| 0 <= k < m < i ==>
                    result@[k] != result@[m],
                forall |k: int| 0 <= k < i - 1 ==>
                    differs_by_one_bit(#[trigger] result@[k], result@[k + 1]),
            decreases total - i,
        {
            let gray_i = i ^ (i >> 1u32);
            let val = start ^ gray_i;

            proof {
                lemma_xor_range(i, start, n_u);

                assert(val == start ^ gray(i));

                assert forall |k: int| 0 <= k < i implies result@[k] != val by {
                    assert(result@[k] == start ^ gray(k as i32));
                    lemma_gray_injective(k as i32, i);
                    lemma_xor_preserves_neq(gray(k as i32), gray(i), start);
                    assert((start ^ gray(k as i32)) != (start ^ gray(i)));
                };

                if i > 0i32 {
                    let prev: i32 = (i - 1i32) as i32;
                    lemma_gray_adjacent(prev);
                    assert((prev + 1i32) as i32 == i) by(bit_vector)
                        requires prev == (i - 1i32) as i32, 0 <= i, i < i32::MAX;
                    lemma_differs_with_xor(gray(prev), gray(i), start);
                }
            }

            result.push(val);
            i = i + 1;
        }

        proof {
            assert(gray(0i32) == 0i32) by {
                assert(0i32 ^ (0i32 >> 1u32) == 0i32) by(bit_vector);
            }
            assert(start ^ 0i32 == start) by(bit_vector);

            let last: i32 = (total - 1i32) as i32;
            lemma_gray_circular(total, n_u);
            lemma_differs_with_xor(gray(0i32), gray(last), start);
        }

        result
    }
}

}
