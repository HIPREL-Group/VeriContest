use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_divisor(n: nat, x: nat) -> bool {
        x >= 1 && x < n && n % x == 0
    }

    pub open spec fn is_winning(n: nat) -> bool
        decreases n
    {
        if n <= 1 {
            false
        } else {
            exists|x: nat| #[trigger] Self::is_divisor(n, x) && !Self::is_winning((n - x) as nat)
        }
    }

    proof fn winning_iff_even(n: nat)
        requires
            n >= 1,
        ensures
            Self::is_winning(n) == (n % 2 == 0),
        decreases n,
    {
        if n == 1 {
        } else if n % 2 == 0 {
            
            Self::winning_iff_even((n - 1) as nat);
            assert(Self::is_divisor(n, 1));
            assert(!Self::is_winning((n - 1) as nat));
        } else {
            
            
            
            
            assert forall|x: nat| #[trigger] Self::is_divisor(n, x) implies Self::is_winning((n - x) as nat)
            by {
                if Self::is_divisor(n, x) {
                    
                    
                    
                    
                    assert(x % 2 != 0) by {
                        if x % 2 == 0 {
                            let k: nat = x / 2;
                            assert(x == 2 * k) by (nonlinear_arith)
                                requires k == x / 2, x % 2 == 0;
                            let q: int = n as int / x as int;
                            assert(q >= 1) by (nonlinear_arith)
                                requires n >= 2, x >= 2, x <= n, n as int % (x as int) == 0, q == n as int / (x as int);
                            assert(n as int == q * x as int) by (nonlinear_arith)
                                requires n as int % (x as int) == 0, q == n as int / (x as int), x >= 1;
                            assert(n as int == 2 * (q * k as int)) by (nonlinear_arith)
                                requires n as int == q * (x as int), x == 2 * k;
                            assert(n % 2 == 0) by (nonlinear_arith)
                                requires n as int == 2 * (q * (k as int)), q >= 1, k >= 1;
                        }
                    };
                    
                    assert((n - x) >= 1) by {
                        assert(x < n);
                    };
                    assert((n - x) % 2 == 0) by (nonlinear_arith)
                        requires n % 2 != 0, x % 2 != 0, x >= 1, x < n;
                    Self::winning_iff_even((n - x) as nat);
                }
            };
        }
    }

    pub fn divisor_game(n: i32) -> (res: bool)
        requires
            1 <= n <= 1000,
        ensures
            res == Self::is_winning(n as nat),
    {
        proof {
            Self::winning_iff_even(n as nat);
        }
        n % 2 == 0
    }
}

}
