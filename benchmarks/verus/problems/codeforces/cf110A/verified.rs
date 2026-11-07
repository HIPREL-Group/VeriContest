use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn count_lucky_digits(n: u64) -> nat
    decreases n,
{
    if n == 0 {
        0nat
    } else {
        let d = (n % 10) as nat;
        let prev = count_lucky_digits(n / 10);
        if d == 4 || d == 7 { prev + 1nat } else { prev }
    }
}

pub open spec fn is_lucky_count(c: nat) -> bool {
    c == 4nat || c == 7nat
}


proof fn lemma_count_le_digits(n: u64, k: u64)
    requires
        (n as nat) < pow10_spec(k),
        k <= 19,
    ensures
        count_lucky_digits(n) <= k as nat,
    decreases n,
{
    if n == 0 {
    } else {
        
        assert(k >= 1);
        assert((n as nat) / 10nat < pow10_spec((k - 1) as u64)) by {
            lemma_pow10_step(k);
        };
        assert((n / 10) as nat == (n as nat) / 10nat);
        lemma_count_le_digits(n / 10, (k - 1) as u64);
    }
}

pub open spec fn pow10_spec(k: u64) -> nat
    decreases k,
{
    if k == 0 { 1nat } else { 10nat * pow10_spec((k - 1) as u64) }
}

proof fn lemma_pow10_step(k: u64)
    requires
        k >= 1,
        k <= 19,
    ensures
        pow10_spec(k) == 10nat * pow10_spec((k - 1) as u64),
{
}

impl Solution {
    pub fn nearly_lucky(n: u64) -> (res: bool)
        requires
            1 <= n <= 1_000_000_000_000_000_000u64,
        ensures
            res == is_lucky_count(count_lucky_digits(n)),
    {
        proof {
            
            assert(pow10_spec(19) == 10000000000000000000nat) by(compute);
            assert((n as nat) < pow10_spec(19));
            lemma_count_le_digits(n, 19);
        }
        let mut count: u64 = 0;
        let mut x: u64 = n;
        while x > 0
            invariant
                count as nat + count_lucky_digits(x) == count_lucky_digits(n),
                count_lucky_digits(n) <= 19nat,
                count <= count_lucky_digits(n),
            decreases x,
        {
            let d = x % 10;
            if d == 4 || d == 7 {
                count += 1;
            }
            x = x / 10;
        }
        count == 4 || count == 7
    }
}

}
