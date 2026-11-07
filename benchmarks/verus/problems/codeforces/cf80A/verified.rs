use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn divides(d: int, n: int) -> bool {
    d > 0 && n > 0 && n % d == 0
}

pub open spec fn is_prime(n: int) -> bool {
    n >= 2 && (forall|d: int| 2 <= d < n ==> !divides(d, n))
}

impl Solution {
    pub fn is_next_prime(n: u32, m: u32) -> (result: bool)
        requires
            2 <= n < m <= 50,
            is_prime(n as int),
        ensures
            result == (is_prime(m as int) && (forall|k: int| n < k < m ==> !is_prime(k))),
    {
        let mut x: u32 = n + 1;
        while x <= m
            invariant
                n + 1 <= x <= m + 1,
                2 <= n < m <= 50,
                forall|k: int| n < k < x ==> !is_prime(k),
            decreases m + 1 - x,
        {
            let mut prime: bool = true;
            let mut d: u32 = 2;
            while d < x
                invariant
                    2 <= d <= x,
                    x >= 2,
                    prime == (forall|dd: int| 2 <= dd < d ==> !divides(dd, x as int)),
                decreases x - d,
            {
                if x % d == 0 {
                    assert(divides(d as int, x as int));
                    prime = false;
                }
                d = d + 1;
            }
            if prime {
                assert(is_prime(x as int));
                if x == m {
                    return true;
                } else {
                    
                    assert(x < m);
                    assert(is_prime(x as int));
                    assert(n < x as int && (x as int) < m as int);
                    return false;
                }
            }
            assert(!prime);
            
            assert(!is_prime(x as int)) by {
                if is_prime(x as int) {
                    assert(forall|dd: int| 2 <= dd < x as int ==> !divides(dd, x as int));
                }
            };
            x = x + 1;
        }
        
        
        false
    }
}

}
