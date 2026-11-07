use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_reverse_inner(n: nat, acc: nat) -> nat
        decreases n
    {
        if n == 0 {
            acc
        } else {
            Self::spec_reverse_inner(n / 10, (acc * 10 + (n % 10)) as nat)
        }
    }

    pub open spec fn spec_reverse(n: nat) -> nat {
        Self::spec_reverse_inner(n, 0)
    }
    
    pub proof fn lemma_reverse_bound(n: nat)
        requires
            n <= 1_000_000, 
        ensures 
            Solution::spec_reverse(n) < 10_000_000,
        decreases n
    {
        reveal_with_fuel(Solution::spec_reverse_inner, 8);
    }

    pub proof fn lemma_reverse_stays_in_range(n: nat)
        requires n <= 1_000_000
        ensures Solution::spec_reverse(n) <= 1_000_000
        decreases n
    {
        reveal_with_fuel(Solution::spec_reverse_inner, 8);
    }

    pub proof fn lemma_reverse_inner_acc_lt_result(n: nat, acc: nat)
        requires 
            n > 0, 
        ensures 
            acc < Self::spec_reverse_inner(n, acc), 
        decreases n,
    {
        reveal_with_fuel(Solution::spec_reverse_inner, 2);
        if n / 10 > 0 {
            Self::lemma_reverse_inner_acc_lt_result(n / 10, acc * 10 + n % 10);
        }
    }

    pub fn is_same_after_reversals(num: i32) -> (res: bool) 
        requires 
            0 <= num <= 1_000_000, 
        ensures
            res == (Self::spec_reverse(Self::spec_reverse(num as nat)) == num as nat)
    {
        let ghost orig_num = num as nat;
        let mut n = num;
        let mut reversed1 = 0i32;
        
        proof {
            Self::lemma_reverse_bound(orig_num);
            Self::lemma_reverse_stays_in_range(orig_num);
        }
        
        while n > 0
            invariant
                0 <= num <= 1_000_000,
                orig_num == num as nat,
                orig_num <= 1_000_000,
                0 <= reversed1 < 10_000_000,
                0 <= n <= num,
                Self::spec_reverse_inner(orig_num, 0) == Self::spec_reverse_inner(n as nat, reversed1 as nat),
                Self::spec_reverse_inner(n as nat, reversed1 as nat) <= 1_000_000,
            decreases n,
        {
            proof {
                Self::lemma_reverse_inner_acc_lt_result(n as nat, reversed1 as nat);
            }
            reversed1 = reversed1 * 10 + n % 10;
            n = n / 10;
        }
        
        let ghost orig_reversed1 = reversed1 as nat;
        let mut m = reversed1;
        let mut reversed2 = 0i32;
        
        proof {
            Self::lemma_reverse_bound(orig_reversed1);
            Self::lemma_reverse_stays_in_range(orig_reversed1);
        }
        
        while m > 0
            invariant
                0 <= reversed1 <= 1_000_000,
                orig_reversed1 == reversed1 as nat,
                orig_reversed1 <= 1_000_000,
                0 <= reversed2 < 10_000_000,
                0 <= m <= reversed1,
                Self::spec_reverse_inner(orig_reversed1, 0) == Self::spec_reverse_inner(m as nat, reversed2 as nat),
                Self::spec_reverse_inner(m as nat, reversed2 as nat) <= 1_000_000,
            decreases m,
        {
            proof {
                Self::lemma_reverse_inner_acc_lt_result(m as nat, reversed2 as nat);
            }
            reversed2 = reversed2 * 10 + m % 10;
            m = m / 10;
        }
        
        reversed2 == num
    }
}

}