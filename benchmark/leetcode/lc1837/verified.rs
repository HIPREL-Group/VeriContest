use vstd::prelude::*;
use vstd::arithmetic::div_mod::{lemma_fundamental_div_mod, lemma_div_decreases};

fn main() {}

verus! {

pub struct Solution;

pub open spec fn digit_sum_base(n: nat, k: nat) -> nat
    decreases n
    when k >= 2
    via digit_sum_base_decreases
{
    if n == 0 {
        0
    } else {
        (n % k) + digit_sum_base(n / k, k)
    }
}

#[verifier::decreases_by]
proof fn digit_sum_base_decreases(n: nat, k: nat) {
    if n > 0 {
        lemma_div_decreases(n as int, k as int);
    }
}

proof fn lemma_digit_sum_bound(n: nat, k: nat)
    requires
        k >= 2,
    ensures
        digit_sum_base(n, k) <= n,
    decreases n,
{
    if n > 0 {
        lemma_div_decreases(n as int, k as int);
        lemma_digit_sum_bound(n / k, k);
        lemma_fundamental_div_mod(n as int, k as int);
        assert(n % k + n / k <= n) by (nonlinear_arith)
            requires
                n as int == k as int * ((n as int) / (k as int)) + (n as int) % (k as int),
                (n as int) / (k as int) >= 0,
                (n as int) % (k as int) >= 0,
                k as int >= 2,
        ;
    }
}

impl Solution {
    pub fn sum_base(n: i32, k: i32) -> (result: i32)
        requires
            1 <= n <= 100,
            2 <= k <= 10,
        ensures
            result == digit_sum_base(n as nat, k as nat) as i32,
    {
        let mut sum: i32 = 0;
        let mut cur: i32 = n;
        proof {
            lemma_digit_sum_bound(n as nat, k as nat);
        }
        while cur > 0
            invariant
                0 <= cur <= n,
                0 <= sum <= n,
                2 <= k <= 10,
                1 <= n <= 100,
                sum + digit_sum_base(cur as nat, k as nat) == digit_sum_base(n as nat, k as nat),
                digit_sum_base(n as nat, k as nat) <= n as nat,
            decreases cur,
        {
            proof {
                lemma_div_decreases(cur as int, k as int);
                lemma_digit_sum_bound(cur as nat / (k as nat), k as nat);
            }
            sum = sum + cur % k;
            cur = cur / k;
        }
        sum
    }
}

} 
