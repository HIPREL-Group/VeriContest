use vstd::prelude::*;

fn main() {}

#[cfg(FALSE)]
mod code_subset {
    use vstd::prelude::*;

    fn main() {}

    pub struct Solution;

    impl Solution {
        pub fn non_special_count(l: i32, r: i32) -> i32 {
            let limit = (r as f64).sqrt() as i32 + 1;
            let mut is_prime = vec![true; limit as usize + 1];
            is_prime[0] = false;
            if limit >= 1 {
                is_prime[1] = false;
            }
            let mut i = 2;
            while i * i <= limit {
                if is_prime[i as usize] {
                    let mut j = i * i;
                    while j <= limit {
                        is_prime[j as usize] = false;
                        j += i;
                    }
                }
                i += 1;
            }
            let mut special_count = 0i32;
            let mut p = 2i32;
            while p <= limit {
                if is_prime[p as usize] {
                    let sq = p * p;
                    if sq >= l && sq <= r {
                        special_count += 1;
                    }
                }
                p += 1;
            }
            r - l + 1 - special_count
        }
    }

    verus! {

    pub struct Solution;

    impl Solution {
        pub open spec fn is_prime(n: int) -> bool {
            n >= 2 && forall |d: int| 2 <= d < n ==> #[trigger] (n % d) != 0
        }

        pub open spec fn count_prime_squares_from(l: int, r: int, p: int) -> int
            decreases if p <= 31623 { 31624 - p } else { 0 },
        {
            if p > 31623 {
                0
            } else {
                let sq = p * p;
                let add = if Self::is_prime(p) && l <= sq && sq <= r { 1 } else { 0 };
                let add: int = add;
                add + Self::count_prime_squares_from(l, r, p + 1)
            }
        }

        pub open spec fn non_special_count_spec(l: i32, r: i32, result: int) -> bool {
            &&& 1 <= l <= r <= 1000000000
            &&& result == r as int - l as int + 1
                - Self::count_prime_squares_from(l as int, r as int, 2)
        }

        pub fn is_prime_exec(n: i32) -> (res: bool)
            requires
                2 <= n <= 31623,
            ensures
                res == Self::is_prime(n as int),
        {
            let mut d = 2i32;

            while d < n
                invariant
                    2 <= n <= 31623,
                    2 <= d <= n,
                    forall |x: int| 2 <= x < d as int ==> #[trigger] (n as int % x) != 0,
                decreases n - d,
            {
                if n % d == 0 {
                    return false;
                }
                d += 1;
            }

            true
        }

        pub fn non_special_count(l: i32, r: i32) -> (result: i32)
            requires
                1 <= l <= r <= 1000000000,
            ensures
                Self::non_special_count_spec(l, r, result as int),
        {
            let limit = (r as f64).sqrt() as i32 + 1;
            let mut is_prime = vec![true; limit as usize + 1];
            is_prime[0] = false;
            if limit >= 1 {
                is_prime[1] = false;
            }
            let mut i = 2;
            while i * i <= limit
                invariant
                    2 <= i <= limit + 1,
                    0 <= limit <= 31624,
            {
                if is_prime[i as usize] {
                    let mut j = i * i;
                    while j <= limit {
                        is_prime[j as usize] = false;
                        j += i;
                    }
                }
                i += 1;
            }
            let mut special_count = 0i32;
            let mut p = 2i32;
            while p <= limit
                invariant
                    2 <= p <= limit + 1,
                    0 <= special_count <= p,
                    special_count as int
                        + Self::count_prime_squares_from(l as int, r as int, p as int)
                        == Self::count_prime_squares_from(l as int, r as int, 2),
            {
                proof {
                    assert(2 <= p <= 31623);
                    assert(0 <= p <= 31623);
                    assert(p * p <= 1000014129) by (nonlinear_arith)
                        requires 0 <= p, p <= 31623;
                    assert(1000014129 <= i32::MAX) by (compute);
                    assert(p * p <= i32::MAX);
                }
                if is_prime[p as usize] {
                    let sq = p * p;
                    if sq >= l && sq <= r {
                        special_count += 1;
                    }
                }
                proof {
                    assert(Self::count_prime_squares_from(l as int, r as int, p as int)
                        == (if Self::is_prime(p as int)
                            && l as int <= p as int * p as int
                            && p as int * p as int <= r as int {
                                1int
                            } else {
                                0int
                            })
                            + Self::count_prime_squares_from(l as int, r as int, p as int + 1));
                }
                p += 1;
            }
            proof {
                assert(p == limit + 1);
                if limit <= 31623 {
                    assert(Self::count_prime_squares_from(l as int, r as int, p as int) == 0);
                }
                assert(special_count as int
                    == Self::count_prime_squares_from(l as int, r as int, 2));
            }
            r - l + 1 - special_count
        }
    }

    }
}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_prime(n: int) -> bool {
        n >= 2 && forall |d: int| 2 <= d < n ==> #[trigger] (n % d) != 0
    }

    pub open spec fn count_prime_squares_from(l: int, r: int, p: int) -> int
        decreases if p <= 31623 { 31624 - p } else { 0 },
    {
        if p > 31623 {
            0
        } else {
            let sq = p * p;
            let add = if Self::is_prime(p) && l <= sq && sq <= r { 1 } else { 0 };
            let add: int = add;
            add + Self::count_prime_squares_from(l, r, p + 1)
        }
    }

    pub open spec fn non_special_count_spec(l: i32, r: i32, result: int) -> bool {
        &&& 1 <= l <= r <= 1000000000
        &&& result == r as int - l as int + 1
            - Self::count_prime_squares_from(l as int, r as int, 2)
    }

    pub fn is_prime_exec(n: i32) -> (res: bool)
        requires
            2 <= n <= 31623,
        ensures
            res == Self::is_prime(n as int),
    {
        let mut d = 2i32;

        while d < n
            invariant
                2 <= n <= 31623,
                2 <= d <= n,
                forall |x: int| 2 <= x < d as int ==> #[trigger] (n as int % x) != 0,
            decreases n - d,
        {
            if n % d == 0 {
                return false;
            }
            d += 1;
        }

        true
    }

    pub fn non_special_count(l: i32, r: i32) -> (result: i32)
        requires
            1 <= l <= r <= 1000000000,
        ensures
            Self::non_special_count_spec(l, r, result as int),
    {
        let mut special_count = 0i32;
        let mut p = 2i32;
        while p <= 31623
            invariant
                2 <= p <= 31624,
                0 <= special_count <= p,
                special_count as int
                    + Self::count_prime_squares_from(l as int, r as int, p as int)
                    == Self::count_prime_squares_from(l as int, r as int, 2),
            decreases 31624 - p,
        {
            let prime = Self::is_prime_exec(p);
            proof {
                assert(2 <= p <= 31623);
                assert(0 <= p <= 31623);
                assert(p * p <= 1000014129) by (nonlinear_arith)
                    requires 0 <= p, p <= 31623;
                assert(1000014129 <= i32::MAX) by (compute);
                assert(p * p <= i32::MAX);
            }
            let sq = p * p;
            let old_special_count = special_count;
            if prime && l <= sq && sq <= r {
                special_count += 1;
            }
            proof {
                assert(prime == Self::is_prime(p as int));
                assert(Self::count_prime_squares_from(l as int, r as int, p as int)
                    == (if Self::is_prime(p as int)
                        && l as int <= p as int * p as int
                        && p as int * p as int <= r as int {
                            1int
                        } else {
                            0int
                        })
                            + Self::count_prime_squares_from(l as int, r as int, p as int + 1));
                if prime && l <= sq && sq <= r {
                    assert(special_count == old_special_count + 1);
                } else {
                    assert(special_count == old_special_count);
                }
                assert(special_count as int
                    + Self::count_prime_squares_from(l as int, r as int, p as int + 1)
                    == Self::count_prime_squares_from(l as int, r as int, 2));
            }
            p += 1;
        }
        proof {
            assert(p == 31624);
            assert(Self::count_prime_squares_from(l as int, r as int, p as int) == 0);
            assert(special_count as int
                == Self::count_prime_squares_from(l as int, r as int, 2));
        }
        r - l + 1 - special_count
    }
}

}
