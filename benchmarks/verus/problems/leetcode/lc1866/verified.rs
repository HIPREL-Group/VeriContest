use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn stirling_mod(n: int, k: int) -> int
    decreases n
{
    if k < 0 || k > n || n < 0 {
        0
    } else if n == k {
        1
    } else if k == 0 {
        0
    } else {
        (stirling_mod(n - 1, k - 1) + ((n - 1) * stirling_mod(n - 1, k)) % 1_000_000_007) % 1_000_000_007
    }
}

proof fn lemma_stirling_mod_bound(n: int, k: int)
    ensures
        0 <= stirling_mod(n, k) < 1_000_000_007,
    decreases n
{
    if k < 0 || k > n || n < 0 {
    } else if n == k {
    } else if k == 0 {
    } else {
        lemma_stirling_mod_bound(n - 1, k - 1);
        lemma_stirling_mod_bound(n - 1, k);
        let a = stirling_mod(n - 1, k - 1);
        let b = stirling_mod(n - 1, k);
        let c = n - 1;
        let m: int = 1_000_000_007;
        assert(c * b >= 0) by (nonlinear_arith)
            requires c >= 0, b >= 0;
    }
}

#[verifier::spinoff_prover]
impl Solution {
    pub fn rearrange_sticks(n: i32, k: i32) -> (result: i32)
        requires
            1 <= n <= 1000,
            1 <= k <= n,
        ensures
            result == stirling_mod(n as int, k as int) as i32,
    {
        let modp: i64 = 1_000_000_007;
        let nn = n as usize;
        let kk = k as usize;
        let mut prev: Vec<i64> = Vec::new();
        let mut idx: usize = 0;
        while idx <= kk
            invariant
                0 <= idx <= kk + 1,
                1 <= kk && kk <= 1000,
                prev.len() == idx,
                forall |j: int| 0 <= j && j < idx as int ==> prev@[j] == 0i64,
            decreases kk + 1 - idx
        {
            prev.push(0i64);
            idx += 1;
        }
        prev.set(0, 1i64);

        proof {
            assert(stirling_mod(0int, 0int) == 1int);
            assert forall |j: int| 1 <= j && j <= kk as int implies #[trigger] stirling_mod(0int, j) == 0int by {
            }
        }

        let mut i: usize = 1;
        while i <= nn
            invariant
                1 <= i <= nn + 1,
                kk == k as usize,
                nn == n as usize,
                1 <= kk && kk <= nn && nn <= 1000,
                modp == 1_000_000_007i64,
                prev.len() == kk + 1,
                forall |j: int| 0 <= j && j <= kk as int ==> 0 <= #[trigger] prev@[j] && prev@[j] < modp,
                forall |j: int| 0 <= j && j <= kk as int ==> prev@[j] as int == stirling_mod((i - 1) as int, j),
            decreases nn + 1 - i
        {
            let mut curr: Vec<i64> = Vec::new();
            let mut idx2: usize = 0;
            while idx2 <= kk
                invariant
                    0 <= idx2 <= kk + 1,
                    1 <= kk && kk <= 1000,
                    curr.len() == idx2,
                    forall |j: int| 0 <= j && j < idx2 as int ==> curr@[j] == 0i64,
                decreases kk + 1 - idx2
            {
                curr.push(0i64);
                idx2 += 1;
            }
            let max_j: usize = if i < kk { i } else { kk };
            let mut j: usize = 1;
            while j <= max_j
                invariant
                    1 <= j <= max_j + 1,
                    curr.len() == kk + 1,
                    prev.len() == kk + 1,
                    max_j == (if i < kk { i } else { kk }),
                    1 <= i && i <= nn,
                    1 <= kk && kk <= nn && nn <= 1000,
                    max_j <= i,
                    max_j <= kk,
                    modp == 1_000_000_007i64,
                    forall |j2: int| 0 <= j2 && j2 <= kk as int ==> 0 <= #[trigger] prev@[j2] && prev@[j2] < modp,
                    forall |j2: int| 0 <= j2 && j2 <= kk as int ==> prev@[j2] as int == stirling_mod((i - 1) as int, j2),
                    forall |j2: int| 1 <= j2 && j2 < j as int ==> 0 <= #[trigger] curr@[j2] && curr@[j2] < modp,
                    forall |j2: int| 1 <= j2 && j2 < j as int ==> #[trigger] curr@[j2] as int == stirling_mod(i as int, j2),
                    curr@[0int] == 0i64,
                    forall |j2: int| j as int <= j2 && j2 <= kk as int ==> #[trigger] curr@[j2] == 0i64,
                decreases max_j + 1 - j
            {
                proof {
                    lemma_stirling_mod_bound((i - 1) as int, (j - 1) as int);
                    lemma_stirling_mod_bound((i - 1) as int, j as int);
                    let a = stirling_mod((i - 1) as int, (j - 1) as int);
                    let b = stirling_mod((i - 1) as int, j as int);
                    let c = (i - 1) as int;
                    assert(c * b >= 0 && c * b <= 999 * 1_000_000_006) by (nonlinear_arith)
                        requires 0 <= c <= 999, 0 <= b < 1_000_000_007;
                    assert(stirling_mod(i as int, j as int) == (a + (c * b) % 1_000_000_007) % 1_000_000_007);
                }
                let term1: i64 = prev[j - 1];
                let term2: i64 = ((i as i64 - 1) * prev[j]) % modp;
                let val: i64 = (term1 + term2) % modp;
                curr.set(j, val);
                j += 1;
            }

            proof {
                let i_int: int = i as int;
                let kk_int: int = kk as int;
                assert(stirling_mod(i_int, 0int) == 0int);

                if i < kk {
                    assert forall |j2: int| i_int < j2 && j2 <= kk_int implies #[trigger] stirling_mod(i_int, j2) == 0int by {
                    }
                }

                assert forall |j2: int| 0 <= j2 && j2 <= kk_int implies #[trigger] curr@[j2] as int == stirling_mod(i_int, j2) by {
                    if j2 == 0 {
                    } else if j2 < j as int && j2 <= max_j as int {
                    } else {
                        assert(curr@[j2] == 0i64);
                        if i < kk {
                            assert(stirling_mod(i_int, j2) == 0int);
                        }
                    }
                }

                assert forall |j2: int| 0 <= j2 && j2 <= kk_int implies 0 <= #[trigger] curr@[j2] && curr@[j2] < 1_000_000_007i64 by {
                    if j2 == 0 {
                    } else if j2 < j as int {
                    } else {
                        assert(curr@[j2] == 0i64);
                    }
                }
            }

            prev = curr;
            i += 1;
        }

        proof {
            lemma_stirling_mod_bound(n as int, k as int);
        }

        prev[kk] as i32
    }
}

}
