use vstd::prelude::*;
use vstd::arithmetic::div_mod::{lemma_fundamental_div_mod, lemma_mod_multiples_vanish};

fn main() {}

verus! {

pub struct Solution;

pub open spec fn repunit(n: int) -> int
    decreases n,
{
    if n <= 0 { 0 }
    else { repunit(n - 1) * 10 + 1 }
}

proof fn mod_mul_add_identity(a: int, k: int)
    requires
        k > 0,
    ensures
        (a * 10 + 1) % k == ((a % k) * 10 + 1) % k,
{
    let q = a / k;
    let r = a % k;
    lemma_fundamental_div_mod(a, k);
    assert(a * 10 + 1 == (r * 10 + 1) + (q * 10) * k) by (nonlinear_arith)
        requires
            a == k * q + r,
    {};
    lemma_mod_multiples_vanish(q * 10, r * 10 + 1, k);
}

impl Solution {
    pub fn smallest_repunit_div_by_k(k: i32) -> (result: i32)
        requires
            1 <= k <= 100_000,
        ensures
            result == -1 || 1 <= result <= k,
            result > 0 ==> repunit(result as int) % (k as int) == 0,
            result > 0 ==> forall|j: int| 1 <= j < result as int ==> repunit(j) % (k as int) != 0,
            result == -1 ==> forall|j: int| 1 <= j <= k as int ==> repunit(j) % (k as int) != 0,
    {
        let mut r: i32 = 0;
        let mut i: i32 = 0;
        proof {
            assert(repunit(0int) == 0);
        }
        while i < k
            invariant
                1 <= k <= 100_000,
                0 <= i <= k,
                0 <= r < k,
                r as int == repunit(i as int) % (k as int),
                forall|j: int| 1 <= j <= i as int ==> repunit(j) % (k as int) != 0,
            decreases k - i,
        {
            proof {
                mod_mul_add_identity(repunit(i as int), k as int);
            }
            r = (r * 10 + 1) % k;
            i = i + 1;
            if r == 0 {
                return i;
            }
        }
        -1
    }
}

}
