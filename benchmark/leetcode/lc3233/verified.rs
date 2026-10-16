use vstd::prelude::*;

fn main() {}

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
            let add: int = if Self::is_prime(p) && l <= sq && sq <= r { 1 } else { 0 };
            add + Self::count_prime_squares_from(l, r, p + 1)
        }
    }

    pub open spec fn non_special_count_spec(l: i32, r: i32, result: int) -> bool {
        &&& 1 <= l <= r <= 1000000000
        &&& result == r as int - l as int + 1
            - Self::count_prime_squares_from(l as int, r as int, 2)
    }

    // What the sieve leaves unmarked once every d < next was processed: no
    // divisor d in [2, next) with d * d <= n.
    pub open spec fn survives(n: int, next: int) -> bool {
        n >= 2 && forall|d: int| 2 <= d < next && d * d <= n ==> #[trigger] (n % d) != 0
    }

    proof fn divisibility_transitive(n: int, d: int, e: int)
        requires 1 <= e <= d <= n, n % d == 0, d % e == 0,
        ensures n % e == 0,
    {
        let q1 = n / d;
        let q2 = d / e;
        assert(n == q1 * d) by(nonlinear_arith)
            requires q1 == n / d, n % d == 0, d >= 1;
        assert(d == q2 * e) by(nonlinear_arith)
            requires q2 == d / e, d % e == 0, e >= 1;
        assert(n == (q1 * q2) * e) by(nonlinear_arith)
            requires n == q1 * d, d == q2 * e;
        assert(n % e == 0) by(nonlinear_arith)
            requires n == (q1 * q2) * e, e >= 1;
    }

    // A composite n has a divisor m >= 2 with m * m <= n.
    proof fn small_divisor(n: int, d: int) -> (m: int)
        requires 2 <= d < n, n % d == 0,
        ensures 2 <= m, m * m <= n, n % m == 0,
    {
        let e = n / d;
        assert(n == d * e) by(nonlinear_arith)
            requires e == n / d, n % d == 0, d >= 1;
        assert(e >= 2) by(nonlinear_arith)
            requires n == d * e, 2 <= d < n;
        if d <= e {
            assert(d * d <= n) by(nonlinear_arith)
                requires n == d * e, 2 <= d <= e;
            d
        } else {
            assert(e * e <= n) by(nonlinear_arith)
                requires n == d * e, 2 <= e < d;
            assert(n % e == 0) by(nonlinear_arith)
                requires n == d * e, e >= 2;
            e
        }
    }

    proof fn count_tail_zero(l: int, r: int, p: int)
        requires 1 <= l <= r <= 1000000000, 1 <= p, p * p > r,
        ensures Self::count_prime_squares_from(l, r, p) == 0,
        decreases if p <= 31623 { 31624 - p } else { 0 },
    {
        if p <= 31623 {
            assert((p + 1) * (p + 1) > r) by(nonlinear_arith)
                requires p >= 1, p * p > r;
            Self::count_tail_zero(l, r, p + 1);
        }
    }

    pub fn non_special_count(l: i32, r: i32) -> (result: i32)
        requires
            1 <= l <= r <= 1000000000,
        ensures
            Self::non_special_count_spec(l, r, result as int),
    {
        let mut root = 0i32;
        while (root + 1) * (root + 1) <= r
            invariant
                1 <= r <= 1000000000,
                0 <= root <= 31622,
                root * root <= r,
                (root + 1) * (root + 1) <= 1000014129,
            decreases 31623 - root,
        {
            assert(root < 31622) by(nonlinear_arith)
                requires root <= 31622, (root + 1) * (root + 1) <= r, r <= 1000000000;
            root += 1;
            assert((root + 1) * (root + 1) <= 1000014129) by(nonlinear_arith)
                requires 0 <= root <= 31622;
        }
        assert(root >= 1) by(nonlinear_arith)
            requires (root + 1) * (root + 1) > r, r >= 1, root >= 0;
        let limit = root + 1;
        proof {
            assert((limit + 1) * (limit + 1) > r) by(nonlinear_arith)
                requires limit == root + 1, (root + 1) * (root + 1) > r, root >= 1;
            Self::count_tail_zero(l as int, r as int, limit as int + 1);
        }
        let mut is_prime = vec![true; limit as usize + 1];
        is_prime[0] = false;
        if limit >= 1 {
            is_prime[1] = false;
        }
        assert forall|n: int| 0 <= n <= limit implies
            #[trigger] is_prime@[n] == Self::survives(n, 2) by {}
        let mut i = 2;
        while i * i <= limit
            invariant
                2 <= limit <= 31623,
                2 <= i <= 178,
                i * i <= 31684,
                is_prime@.len() == limit + 1,
                forall|n: int| 0 <= n <= limit ==> #[trigger] is_prime@[n] == Self::survives(n, i as int),
            decreases limit + 1 - i,
        {
            assert(i <= 177 && i <= limit) by(nonlinear_arith)
                requires i * i <= limit, limit <= 31623, i >= 2;
            if is_prime[i as usize] {
                let mut j = i * i;
                proof {
                    assert(j % i == 0) by(nonlinear_arith) requires j == i * i, i >= 2;
                }
                while j <= limit
                    invariant
                        2 <= limit <= 31623,
                        2 <= i <= 177,
                        i * i <= j <= limit + i,
                        j % i == 0,
                        is_prime@.len() == limit + 1,
                        forall|n: int| 0 <= n <= limit ==> #[trigger] is_prime@[n]
                            == (Self::survives(n, i as int) && !(i * i <= n < j && n % (i as int) == 0)),
                    decreases limit + i - j,
                {
                    let ghost old_j = j;
                    let ghost old_marks = is_prime@;
                    is_prime[j as usize] = false;
                    j += i;
                    proof {
                        assert(j % i == 0) by(nonlinear_arith)
                            requires j == old_j + i, old_j % i == 0, i >= 2;
                        assert forall|n: int| 0 <= n <= limit implies #[trigger] is_prime@[n]
                            == (Self::survives(n, i as int) && !(i * i <= n < j && n % (i as int) == 0)) by {
                            if n != old_j && old_j < n < j && n % (i as int) == 0 {
                                assert(false) by(nonlinear_arith)
                                    requires old_j < n < old_j + i, n % (i as int) == 0, old_j % i == 0, i >= 2;
                            }
                            if n != old_j {
                                assert(is_prime@[n] == old_marks[n]);
                            }
                        }
                    }
                }
                proof {
                    assert forall|n: int| 0 <= n <= limit implies
                        #[trigger] is_prime@[n] == Self::survives(n, i + 1) by {
                        if Self::survives(n, i as int) && !(i * i <= n && n % (i as int) == 0) {
                            assert forall|d: int| 2 <= d < i + 1 && d * d <= n implies #[trigger] (n % d) != 0 by {
                                if d < i {
                                    assert(Self::survives(n, i as int));
                                }
                            }
                        }
                    }
                }
            } else {
                proof {
                    // i is composite: some d < i with d * d <= i divides it, and
                    // every multiple of i was already marked through d.
                    assert(!Self::survives(i as int, i as int));
                    let d = choose|d: int| 2 <= d < i && d * d <= i && #[trigger] ((i as int) % d) == 0;
                    assert forall|n: int| 0 <= n <= limit implies
                        #[trigger] is_prime@[n] == Self::survives(n, i + 1) by {
                        if Self::survives(n, i as int) {
                            assert forall|e: int| 2 <= e < i + 1 && e * e <= n implies #[trigger] (n % e) != 0 by {
                                if e == i && n % e == 0 {
                                    assert(i <= n) by(nonlinear_arith) requires i * i <= n, i >= 2;
                                    Self::divisibility_transitive(n, i as int, d);
                                    assert(d * d <= n);
                                }
                            }
                        }
                    }
                }
            }
            i += 1;
            assert(i * i <= 31684) by(nonlinear_arith) requires 2 <= i <= 178;
        }
        proof {
            assert forall|n: int| 2 <= n <= limit implies #[trigger] is_prime@[n] == Self::is_prime(n) by {
                if Self::is_prime(n) {
                    assert forall|d: int| 2 <= d < i && d * d <= n implies #[trigger] (n % d) != 0 by {
                        assert(d < n) by(nonlinear_arith) requires d >= 2, d * d <= n;
                    }
                }
                if Self::survives(n, i as int) {
                    assert forall|d: int| 2 <= d < n implies #[trigger] (n % d) != 0 by {
                        if n % d == 0 {
                            let m = Self::small_divisor(n, d);
                            assert(m < i) by(nonlinear_arith)
                                requires m * m <= n, n <= limit, limit < i * i, m >= 2, i >= 2;
                            assert(n % m != 0);
                        }
                    }
                }
            }
        }
        let mut special_count = 0i32;
        let mut p = 2i32;
        while p <= limit
            invariant
                1 <= l <= r <= 1000000000,
                2 <= limit <= 31623,
                2 <= p <= limit + 1,
                is_prime@.len() == limit + 1,
                forall|n: int| 2 <= n <= limit ==> #[trigger] is_prime@[n] == Self::is_prime(n),
                0 <= special_count <= p,
                special_count as int + Self::count_prime_squares_from(l as int, r as int, p as int)
                    == Self::count_prime_squares_from(l as int, r as int, 2),
            decreases limit + 1 - p,
        {
            assert(p * p <= 1000014129) by(nonlinear_arith)
                requires 2 <= p <= 31623;
            if is_prime[p as usize] {
                let sq = p * p;
                if sq >= l && sq <= r {
                    special_count += 1;
                }
            }
            proof {
                assert(Self::count_prime_squares_from(l as int, r as int, p as int)
                    == (if Self::is_prime(p as int) && l <= p * p && p * p <= r { 1int } else { 0int })
                        + Self::count_prime_squares_from(l as int, r as int, p as int + 1));
            }
            p += 1;
        }
        r - l + 1 - special_count
    }
}

}
