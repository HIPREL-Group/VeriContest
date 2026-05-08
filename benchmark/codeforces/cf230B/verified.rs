use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn is_prime(n: int) -> bool {
    2 <= n && forall|d: int| 2 <= d && d <= n / d ==> #[trigger] (n % d) != 0
}

pub open spec fn is_t_prime(x: int) -> bool {
    exists|p: int| 2 <= p && p * p == x && is_prime(p)
}

proof fn lemma_unique_square_root(x: int, r: int, p: int)
    requires
        0 <= r,
        0 <= p,
        r * r <= x,
        x < (r + 1) * (r + 1),
        p * p == x,
    ensures
        p == r,
{
    assert(r <= p) by (nonlinear_arith)
        requires
            0 <= r,
            0 <= p,
            r * r <= p * p,
    {
    }
    if r < p {
        assert((r + 1) * (r + 1) <= p * p) by (nonlinear_arith)
            requires
                0 <= r,
                0 <= p,
                r < p,
        {
        }
        assert(false);
    }
    assert(p == r) by (nonlinear_arith)
        requires
            r <= p,
            !(r < p),
    {
    }
}

impl Solution {
    fn floor_sqrt(x: u64) -> (r: u64)
        requires
            1u64 <= x <= 1_000_000_000_000u64,
        ensures
            r <= 1_000_000u64,
            r * r <= x,
            x < (r + 1) * (r + 1),
    {
        let mut lo = 1u64;
        let mut hi = 1_000_001u64;
        while lo < hi
            invariant
                1u64 <= x <= 1_000_000_000_000u64,
                1u64 <= lo <= hi <= 1_000_001u64,
                (lo - 1) * (lo - 1) <= x,
                x < hi * hi,
            decreases hi - lo,
        {
            let mid = lo + (hi - lo) / 2;
            proof {
                assert(lo <= mid) by (nonlinear_arith)
                    requires
                        lo < hi,
                        mid == lo + (hi - lo) / 2,
                {
                }
                assert(mid < hi) by (nonlinear_arith)
                    requires
                        lo < hi,
                        mid == lo + (hi - lo) / 2,
                {
                }
                assert(mid <= 1_000_000u64) by (nonlinear_arith)
                    requires
                        mid < hi,
                        hi <= 1_000_001u64,
                {
                }
            }
            proof {
                assert(mid * mid <= 18_446_744_073_709_551_615u64) by (nonlinear_arith)
                    requires
                        mid <= 1_000_000u64,
                {
                }
            }
            if mid * mid <= x {
                lo = mid + 1;
                proof {
                    assert((lo - 1) == mid);
                    assert((lo - 1) * (lo - 1) <= x);
                }
            } else {
                hi = mid;
                proof {
                    assert(x < hi * hi);
                }
            }
        }
        let r = lo - 1;
        proof {
            assert(lo == hi);
            assert(r <= 1_000_000u64) by (nonlinear_arith)
                requires
                    lo <= 1_000_001u64,
                    r == lo - 1,
            {
            }
            assert(r * r <= x);
            assert(x < (r + 1) * (r + 1));
        }
        r
    }

    fn is_prime_runtime(n: u64) -> (res: bool)
        requires
            n <= 1_000_000u64,
        ensures
            res == is_prime(n as int),
    {
        if n < 2 {
            return false;
        }
        let mut d = 2u64;
        while d <= n / d
            invariant
                2u64 <= n <= 1_000_000u64,
                2u64 <= d <= n + 1,
                forall|e: int| 2 <= e < (d as int) ==> #[trigger] ((n as int) % e) != 0,
            decreases n - d + 1,
        {
            if n % d == 0 {
                proof {
                    assert(!is_prime(n as int)) by {
                        assert(2 <= d as int && d as int <= (n as int) / (d as int));
                        assert((n as int) % (d as int) == 0);
                    }
                }
                return false;
            }
            proof {
                assert forall|e: int| 2 <= e < (d as int) + 1 implies #[trigger] ((n as int) % e) != 0 by {
                    if e < (d as int) {
                    } else {
                        assert(e == d as int);
                        assert((n as int) % e == n % d);
                    }
                }
            }
            d += 1;
        }
        proof {
            if !is_prime(n as int) {
                let e = choose|e: int| 2 <= e && e <= (n as int) / e && #[trigger] ((n as int) % e) == 0;
                assert(e < (d as int)) by (nonlinear_arith)
                    requires
                        2 <= d as int,
                        d as int > n as int / d as int,
                        2 <= e,
                        e <= n as int / e,
                {
                }
                assert((n as int) % e != 0);
                assert(false);
            }
        }
        true
    }

    pub fn classify_t_primes(nums: Vec<u64>) -> (res: Vec<bool>)
        requires
            1 <= nums.len() <= 100_000,
            forall|i: int| 0 <= i < nums.len() ==> 1u64 <= #[trigger] nums[i] <= 1_000_000_000_000u64,
        ensures
            res.len() == nums.len(),
            forall|i: int| 0 <= i < res.len() ==> #[trigger] res[i] == is_t_prime(nums[i] as int),
    {
        let mut res = Vec::new();
        let mut i = 0usize;
        while i < nums.len()
            invariant
                1 <= nums.len() <= 100_000,
                forall|k: int| 0 <= k < nums.len() ==> 1u64 <= #[trigger] nums[k] <= 1_000_000_000_000u64,
                0 <= i <= nums.len(),
                res.len() == i,
                forall|k: int| 0 <= k < i ==> #[trigger] res[k] == is_t_prime(nums[k] as int),
            decreases nums.len() - i,
        {
            let x = nums[i];
            let root = Self::floor_sqrt(x);
            let answer = if root * root == x {
                Self::is_prime_runtime(root)
            } else {
                false
            };
            let ghost old_res = res@;
            let cur = i;
            proof {
                if root * root == x {
                    assert(answer == is_prime(root as int));
                    assert(answer == is_t_prime(x as int)) by {
                        if answer {
                            assert(exists|p: int| 2 <= p && p * p == x as int && is_prime(p)) by {
                                let p = root as int;
                            }
                        } else {
                            if is_t_prime(x as int) {
                                let p = choose|p: int| 2 <= p && p * p == x as int && is_prime(p);
                                lemma_unique_square_root(x as int, root as int, p);
                                assert(root as int == p);
                                assert(is_prime(root as int));
                                assert(answer);
                                assert(false);
                            }
                        }
                    }
                } else {
                    assert(answer == false);
                    assert(!is_t_prime(x as int)) by {
                        if is_t_prime(x as int) {
                            let p = choose|p: int| 2 <= p && p * p == x as int && is_prime(p);
                            lemma_unique_square_root(x as int, root as int, p);
                            assert(root as int == p);
                            assert(root * root == x);
                            assert(false);
                        }
                    }
                }
            }
            res.push(answer);
            i += 1;
            proof {
                assert(res@ == old_res.push(answer));
                assert(res.len() == i);
                assert forall|k: int| 0 <= k < i implies #[trigger] res[k] == is_t_prime(nums[k] as int) by {
                    if k < cur as int {
                        assert(res[k] == old_res[k]);
                    } else {
                        assert(k == cur as int);
                        assert(res[k] == answer);
                    }
                }
            }
        }
        res
    }
}

}
