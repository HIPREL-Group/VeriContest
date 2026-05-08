use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn round_sum(n: int) -> int { n * (n + 1) / 2 }

pub open spec fn after_full_rounds(n: int, m: int) -> int {
    if round_sum(n) > 0 { m % round_sum(n) } else { m }
}

pub open spec fn final_remainder(n: int, rem: int, walrus: int) -> int
    decreases (n + 1) - walrus,
{
    if walrus < 1 || walrus > n || rem < walrus {
        rem
    } else {
        final_remainder(n, rem - walrus, walrus + 1)
    }
}

proof fn lemma_final_walrus_nonneg(n: int, rem: int, walrus: int)
    requires
        1 <= n,
        0 <= rem,
        1 <= walrus,
    ensures
        final_remainder(n, rem, walrus) >= 0,
    decreases (n + 1) - walrus,
{
    if walrus < 1 || walrus > n || rem < walrus {
    } else {
        lemma_final_walrus_nonneg(n, rem - walrus, walrus + 1);
    }
}

proof fn lemma_round_sum_pos(n: int)
    requires
        1 <= n,
    ensures
        round_sum(n) >= 1,
{
    assert(n * (n + 1) / 2 >= 1) by (nonlinear_arith) requires n >= 1;
}

impl Solution {
    pub fn presenter_chips(n: u32, m: u32) -> (result: u32)
        requires
            1 <= n <= 50,
            1 <= m <= 10000,
        ensures
            result as int == final_remainder(n as int, after_full_rounds(n as int, m as int), 1),
            result < n,
    {
        proof {
            lemma_round_sum_pos(n as int);
            assert(n * (n + 1) / 2 <= 50 * 51 / 2) by (nonlinear_arith) requires n <= 50u32;
        }
        let r_sum: u32 = n * (n + 1) / 2;
        let mut remaining: u32 = m % r_sum;
        let initial_remaining: u32 = remaining;
        let mut walrus: u32 = 1;
        let mut subtracted: u32 = 0;
        proof {
            assert(remaining as int == after_full_rounds(n as int, m as int));
            assert(remaining < r_sum);
        }
        while walrus <= n && remaining >= walrus
            invariant
                1 <= walrus <= n + 1,
                walrus <= 51,
                1 <= n <= 50,
                remaining < r_sum,
                r_sum == n * (n + 1) / 2,
                subtracted as int == (walrus as int - 1) * walrus as int / 2,
                remaining as int + subtracted as int == initial_remaining as int,
                initial_remaining == m % r_sum,
                final_remainder(n as int, after_full_rounds(n as int, m as int), 1) ==
                    final_remainder(n as int, remaining as int, walrus as int),
            decreases (n + 1) - walrus,
        {
            remaining = remaining - walrus;
            subtracted = subtracted + walrus;
            walrus = walrus + 1;
            proof {
                assert(subtracted as int == (walrus as int - 1) * walrus as int / 2) by (nonlinear_arith)
                    requires
                        subtracted as int == (walrus as int - 2) * (walrus as int - 1) / 2 + (walrus as int - 1),
                        walrus >= 2;
            }
        }
        proof {
            assert(remaining as int == final_remainder(n as int, remaining as int, walrus as int));
            
            
            
            
            
            if walrus > n as u32 {
                assert(walrus == n + 1);
                assert(subtracted as int == n as int * (n as int + 1) / 2);
                assert(subtracted == r_sum);
                assert(remaining as int + r_sum as int == initial_remaining as int);
                assert(initial_remaining < r_sum);
                assert(false);
            }
            assert(walrus <= n);
            assert(remaining < walrus);
            assert(remaining < n);
        }
        remaining
    }
}

}
