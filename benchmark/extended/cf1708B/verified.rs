use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_first_mult(l: int, k: int) -> int {
    (l + k - 1) / k * k
}

pub open spec fn feasible(n: int, l: int, r: int) -> bool {
    forall|j: int|
        #![trigger spec_first_mult(l, j + 1)]
        0 <= j && j < n ==> spec_first_mult(l, j + 1) <= r && spec_first_mult(l, j + 1) >= l
}

pub open spec fn seq_matches_witness(n: int, l: int, r: int, s: Seq<i32>) -> bool {
    s.len() == n
        && (forall|i: int|
            0 <= i && i < n ==> s[i] == spec_first_mult(l, i + 1))
}

proof fn lemma_i32_div_mod_nonneg(a: i32, b: i32)
    requires
        a >= 0,
        b > 0,
    ensures
        (a / b) as int == (a as int) / (b as int),
        (a % b) as int == (a as int) % (b as int),
{
}

proof fn lemma_i32_add_sub3(l: i32, k: i32)
    requires
        l >= 1,
        k >= 1,
    ensures
        (l + k - 1) as int == l as int + k as int - 1,
{
}

proof fn lemma_i64_div_mod_nonneg(a: i64, b: i64)
    requires
        a >= 0,
        b > 0,
    ensures
        (a / b) as int == (a as int) / (b as int),
        (a % b) as int == (a as int) % (b as int),
{
}

proof fn lemma_i64_mul(a: i64, b: i64)
    requires
        a >= 0,
        b >= 0,
    ensures
        (a * b) as int == a as int * b as int,
{
}

proof fn lemma_i64_div_mul_le(num: i64, k: i64)
    requires
        num >= 0,
        k > 0,
    ensures
        (num / k) * k <= num,
{
    assert((num / k) * k <= num) by(nonlinear_arith)
        requires
            num >= 0,
            k > 0;
}

proof fn lemma_spec_first_mult_ge_l(l: int, k: int)
    requires
        l >= 1,
        k >= 1,
    ensures
        spec_first_mult(l, k) >= l,
{
    assert(spec_first_mult(l, k) == (l + k - 1) / k * k);
    assert((l + k - 1) / k * k >= l) by(nonlinear_arith)
        requires
            l >= 1,
            k >= 1;
}

proof fn lemma_not_feasible(n: int, l: int, r: int, k_bad: int)
    requires
        1 <= k_bad && k_bad <= n,
        spec_first_mult(l, k_bad) > r,
    ensures
        !feasible(n, l, r),
{
    let j_bad = k_bad - 1;
    assert(0 <= j_bad && j_bad < n);
    assert(spec_first_mult(l, k_bad) == spec_first_mult(l, j_bad + 1));
    assert(!(spec_first_mult(l, j_bad + 1) <= r));
    assert(!feasible(n, l, r));
}

impl Solution {
    #[verifier::exec_allows_no_decreases_clause]
    pub fn construct_gcd_array(n: usize, l: i32, r: i32) -> (res: (bool, Vec<i32>))
        requires
            1 <= n <= 100_000,
            1 <= l <= r <= 1_000_000_000,
        ensures
            res.0 == feasible(n as int, l as int, r as int),
            !res.0 ==> res.1.len() == 0,
            res.0 ==> res.1.len() == n,
            res.0 ==> seq_matches_witness(n as int, l as int, r as int, res.1@),
            res.0 ==> (forall|i: int|
                0 <= i && i < n ==> l as int <= #[trigger] res.1@[i] && res.1@[i] <= r as int),
            res.0 ==> (forall|i: int|
                0 <= i && i < n ==> 1 <= #[trigger] res.1@[i]),
    {
        let mut a: Vec<i32> = Vec::new();
        let mut t: usize = 0;
        while t < n
            invariant
                a.len() == t,
                t <= n,
            decreases n - t
        {
            a.push(0i32);
            t = t + 1;
        }
        let mut i: usize = 0;
        while i < n
            invariant
                a.len() == n,
                0 <= i && i <= n,
                n <= 100_000,
                1 <= l <= r <= 1_000_000_000,
                forall|j: int|
                    #![trigger a@[j]]
                    0 <= j && j < i ==> a@[j] == spec_first_mult(l as int, j + 1),
                forall|j: int|
                    #![trigger spec_first_mult(l as int, j + 1)]
                    0 <= j && j < i ==> spec_first_mult(l as int, j + 1) <= r as int
                        && spec_first_mult(l as int, j + 1) >= l as int,
            decreases n - i
        {
            let k = (i + 1) as i32;
            proof {
                assert(i < n);
                assert(i + 1 <= n);
                assert((i + 1) as int <= n as int);
                assert((i + 1) as int >= 1);
                assert(k as int == (i + 1) as int);
                assert(k >= 1);
            }
            let k64 = k as i64;
            proof {
                assert(k64 > 0);
            }
            let num: i64 = l as i64 + k64 - 1;
            proof {
                assert(num >= 0);
            }
            let q = num / k64;
            proof {
                lemma_i64_div_mul_le(num, k64);
                assert(q * k64 <= num);
                assert(num <= 1_000_000_000i64 + 100_000i64);
                assert(q * k64 <= 2_147_483_647i64);
            }
            let first = (q * k64) as i32;
            if first > r {
                proof {
                    let kk = (i + 1) as int;
                    let li = l as int;
                    let ki = k as int;
                    assert(1 <= kk && kk <= n as int);
                    lemma_i32_add_sub3(l, k);
                    assert(num as int == li + ki - 1);
                    lemma_i64_div_mod_nonneg(num, k64);
                    assert(q as int == (li + ki - 1) / ki);
                    lemma_i64_mul(q, k64);
                    assert((q * k64) as int == q as int * ki);
                    assert(first as int == (li + ki - 1) / ki * ki);
                    assert((li + ki - 1) / ki * ki == spec_first_mult(li, ki));
                    assert(spec_first_mult(l as int, kk) > r as int);
                    lemma_not_feasible(n as int, l as int, r as int, kk);
                }
                return (false, Vec::new());
            }
            proof {
                let li = l as int;
                let ki = k as int;
                lemma_i32_add_sub3(l, k);
                assert(num as int == li + ki - 1);
                lemma_i64_div_mod_nonneg(num, k64);
                assert(q as int == (li + ki - 1) / ki);
                lemma_i64_mul(q, k64);
                assert((q * k64) as int == q as int * ki);
                assert(first as int == (li + ki - 1) / ki * ki);
                assert((li + ki - 1) / ki * ki == spec_first_mult(li, ki));
                assert(spec_first_mult(li, ki) <= r as int);
                lemma_spec_first_mult_ge_l(li, ki);
                assert(spec_first_mult(li, ki) >= li);
            }
            a.set(i, first);
            i = i + 1;
        }
        proof {
            assert(feasible(n as int, l as int, r as int));
            assert(seq_matches_witness(n as int, l as int, r as int, a@));
        }
        (true, a)
    }
}

}
