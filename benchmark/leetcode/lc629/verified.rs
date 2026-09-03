use vstd::prelude::*;
use vstd::arithmetic::div_mod::{lemma_add_mod_noop_right, lemma_sub_mod_noop};

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn modv() -> int {
        1000000007
    }

    pub open spec fn lim(i: int, j: int) -> int
        recommends
            1 <= i <= 1000,
            0 <= j <= 1000,
    {
        if j < i - 1 { j } else { i - 1 }
    }

    pub open spec fn inv_count(i: int, j: int) -> int
        decreases if i < 0 { 0nat } else { i as nat }, 1nat, 0nat,
    {
        if i < 0 || i > 1000 || j < 0 || j > 1000 {
            0
        } else if i == 0 {
            if j == 0 { 1 } else { 0 }
        } else {
            Self::prefix(i, j, Self::lim(i, j) + 1)
        }
    }

    pub open spec fn prefix(i: int, j: int, t: int) -> int
        decreases if i < 0 { 0nat } else { i as nat }, 0nat, if t < 0 { 0nat } else { t as nat },
    {
        if i <= 0 || j < 0 || j > 1000 || t <= 0 {
            0
        } else {
            (Self::prefix(i, j, t - 1) + Self::inv_count(i - 1, j - (t - 1))) % Self::modv()
        }
    }

    proof fn lemma_inv_count_range(i: int, j: int)
        ensures
            0 <= Self::inv_count(i, j) < Self::modv(),
        decreases if i < 0 { 0nat } else { i as nat }, 1nat, 0nat,
    {
        if i < 0 || i > 1000 || j < 0 || j > 1000 {
        } else if i == 0 {
        } else {
            Self::lemma_prefix_range(i, j, Self::lim(i, j) + 1);
        }
    }

    proof fn lemma_prefix_range(i: int, j: int, t: int)
        ensures
            0 <= Self::prefix(i, j, t) < Self::modv(),
        decreases if i < 0 { 0nat } else { i as nat }, 0nat, if t < 0 { 0nat } else { t as nat },
    {
        if i <= 0 || j < 0 || j > 1000 || t <= 0 {
        } else {
            Self::lemma_prefix_range(i, j, t - 1);
            Self::lemma_inv_count_range(i - 1, j - (t - 1));
        }
    }

    proof fn lemma_prefix_shift(i: int, j: int, t: int)
        requires
            i >= 1,
            j >= 1,
            j <= 1000,
            t >= 1,
        ensures
            Self::prefix(i, j, t) == (Self::inv_count(i - 1, j) + Self::prefix(i, j - 1, t - 1)) % Self::modv(),
        decreases t,
    {
        assert(Self::modv() > 0);
        Self::lemma_inv_count_range(i - 1, j);
        Self::lemma_prefix_range(i, j - 1, t - 1);
        if t == 1 {
            assert(Self::prefix(i, j, 1)
                == (Self::prefix(i, j, 0) + Self::inv_count(i - 1, j - 0)) % Self::modv());
            assert(Self::prefix(i, j, 0) == 0);
            assert(Self::prefix(i, j - 1, 0) == 0);
        } else {
            Self::lemma_prefix_shift(i, j, t - 1);
            Self::lemma_prefix_range(i, j - 1, t - 2);
            Self::lemma_inv_count_range(i - 1, j - (t - 1));
            assert(Self::prefix(i, j, t)
                == (Self::prefix(i, j, t - 1) + Self::inv_count(i - 1, j - (t - 1))) % Self::modv());
            let a: int = Self::inv_count(i - 1, j) + Self::prefix(i, j - 1, t - 2);
            let b: int = Self::inv_count(i - 1, j - (t - 1));
            assert(Self::prefix(i, j, t - 1) == a % Self::modv());
            lemma_add_mod_noop_right(b, a, Self::modv());
            assert((b + (a % Self::modv())) % Self::modv() == (b + a) % Self::modv());
            assert(Self::prefix(i, j, t) == (b + a) % Self::modv());
            assert(j - (t - 1) == (j - 1) - (t - 2));
            let c: int = Self::prefix(i, j - 1, t - 2) + Self::inv_count(i - 1, (j - 1) - (t - 2));
            assert(b + a == Self::inv_count(i - 1, j) + c);
            assert(Self::prefix(i, j - 1, t - 1)
                == (Self::prefix(i, j - 1, t - 2) + Self::inv_count(i - 1, (j - 1) - (t - 2))) % Self::modv());
            assert(Self::prefix(i, j - 1, t - 1) == c % Self::modv());
            lemma_add_mod_noop_right(Self::inv_count(i - 1, j), c, Self::modv());
            assert((Self::inv_count(i - 1, j) + (c % Self::modv())) % Self::modv()
                == (Self::inv_count(i - 1, j) + c) % Self::modv());
            assert(Self::prefix(i, j, t) == (Self::inv_count(i - 1, j) + Self::prefix(i, j - 1, t - 1)) % Self::modv());
        }
    }

    proof fn lemma_window_step_zero(i: int)
        requires
            1 <= i <= 1000,
        ensures
            Self::inv_count(i, 0) == Self::inv_count(i - 1, 0) % Self::modv(),
    {
        assert(Self::lim(i, 0) == 0);
        assert(Self::inv_count(i, 0) == Self::prefix(i, 0, 1));
        assert(Self::prefix(i, 0, 1) == (Self::prefix(i, 0, 0) + Self::inv_count(i - 1, 0 - 0)) % Self::modv());
        assert(Self::prefix(i, 0, 0) == 0);
    }

    proof fn lemma_window_step_no_sub(i: int, j: int)
        requires
            1 <= i <= 1000,
            1 <= j <= 1000,
            j < i,
        ensures
            (Self::inv_count(i, j - 1) + Self::inv_count(i - 1, j)) % Self::modv() == Self::inv_count(i, j),
    {
        assert(Self::lim(i, j) == j);
        assert(Self::lim(i, j - 1) == j - 1);
        assert(Self::inv_count(i, j) == Self::prefix(i, j, j + 1));
        assert(Self::inv_count(i, j - 1) == Self::prefix(i, j - 1, j));
        Self::lemma_prefix_shift(i, j, j + 1);
        assert(Self::prefix(i, j, j + 1) == (Self::inv_count(i - 1, j) + Self::prefix(i, j - 1, j)) % Self::modv());
    }

    proof fn lemma_window_step_sub(i: int, j: int)
        requires
            1 <= i <= 1000,
            1 <= j <= 1000,
            j >= i,
        ensures
            (Self::inv_count(i, j - 1) + Self::inv_count(i - 1, j) - Self::inv_count(i - 1, j - i)) % Self::modv()
                == Self::inv_count(i, j),
    {
        assert(Self::modv() > 0);
        assert(Self::lim(i, j) == i - 1);
        assert(Self::lim(i, j - 1) == i - 1);
        Self::lemma_prefix_shift(i, j, i);
        assert(Self::prefix(i, j, i) == Self::inv_count(i, j));
        assert(Self::prefix(i, j, i)
            == (Self::inv_count(i - 1, j) + Self::prefix(i, j - 1, i - 1)) % Self::modv());
        assert(Self::prefix(i, j - 1, i) == Self::inv_count(i, j - 1));
        assert(Self::prefix(i, j - 1, i)
            == (Self::prefix(i, j - 1, i - 1) + Self::inv_count(i - 1, (j - 1) - (i - 1))) % Self::modv());
        assert((j - 1) - (i - 1) == j - i);
        Self::lemma_inv_count_range(i - 1, j - i);
        Self::lemma_prefix_range(i, j - 1, i - 1);
        let p: int = Self::prefix(i, j - 1, i - 1);
        let q: int = Self::inv_count(i - 1, j - i);
        assert(Self::inv_count(i, j - 1) == (p + q) % Self::modv());
        lemma_sub_mod_noop(p + q, q, Self::modv());
        assert(((p + q) % Self::modv() - q % Self::modv()) % Self::modv() == ((p + q) - q) % Self::modv());
        assert(((p + q) - q) % Self::modv() == p % Self::modv());
        assert(p % Self::modv() == p);
        assert((Self::inv_count(i, j - 1) - q % Self::modv()) % Self::modv() == p);
        assert(q % Self::modv() == q);
        assert((Self::inv_count(i, j - 1) - q) % Self::modv() == p);
        Self::lemma_inv_count_range(i - 1, j);
        lemma_add_mod_noop_right(Self::inv_count(i - 1, j), Self::inv_count(i, j - 1) - q, Self::modv());
        assert((Self::inv_count(i - 1, j) + ((Self::inv_count(i, j - 1) - q) % Self::modv())) % Self::modv()
            == (Self::inv_count(i - 1, j) + (Self::inv_count(i, j - 1) - q)) % Self::modv());
        assert(Self::inv_count(i, j)
            == (Self::inv_count(i - 1, j) + (Self::inv_count(i, j - 1) - q)) % Self::modv());
        assert(Self::inv_count(i - 1, j) + (Self::inv_count(i, j - 1) - q)
            == Self::inv_count(i, j - 1) + Self::inv_count(i - 1, j) - q);
    }

    pub fn k_inverse_pairs(n: i32, k: i32) -> (result: i32)
        requires
            1 <= n <= 1000,
            0 <= k <= 1000,
        ensures
            0 <= (result as int),
            (result as int) < Self::modv(),
            result as int == Self::inv_count(n as int, k as int),
    {
        let m: i64 = 1000000007;
        assert(0 < m);
        assert(m <= i32::MAX as i64);

        let mut dp: Vec<i32> = Vec::new();
        let mut t: usize = 0;
        while t <= 1000
            invariant
                t <= 1001,
                dp.len() == t,
                forall|u: int| 0 <= u && u < t ==> #[trigger] dp[u] == 0,
            decreases 1001 - t,
        {
            dp.push(0);
            t += 1;
        }
        dp[0] = 1;

        let mut i: i32 = 1;
        while i <= n
            invariant
                1 <= n <= 1000,
                0 <= k <= 1000,
                m == 1000000007i64,
                dp.len() == 1001,
                1 <= i <= n + 1,
                forall|u: int| 0 <= u && u <= k ==> 0 <= (dp[u] as int),
                forall|u: int| 0 <= u && u <= k ==> (dp[u] as int) < m,
                forall|u: int| 0 <= u && u <= k ==> (dp[u] as int) == Self::inv_count((i - 1) as int, u),
            decreases n - i + 1,
        {
            let mut next: Vec<i32> = Vec::new();
            let mut t2: usize = 0;
            while t2 <= 1000
                invariant
                    t2 <= 1001,
                    next.len() == t2,
                    forall|u: int| 0 <= u && u < t2 ==> #[trigger] next[u] == 0,
                decreases 1001 - t2,
            {
                next.push(0);
                t2 += 1;
            }

            let mut j: i32 = 0;
            let mut window: i64 = 0;
            while j <= k
                invariant
                    1 <= n <= 1000,
                    0 <= k <= 1000,
                    m == 1000000007i64,
                    dp.len() == 1001,
                    next.len() == 1001,
                    0 <= j <= k + 1,
                    1 <= i <= n,
                    forall|u: int| 0 <= u && u <= k ==> 0 <= (dp[u] as int),
                    forall|u: int| 0 <= u && u <= k ==> (dp[u] as int) < m,
                    forall|u: int| 0 <= u && u <= k ==> (dp[u] as int) == Self::inv_count((i - 1) as int, u),
                    forall|u: int| 0 <= u && u < j ==> 0 <= (next[u] as int),
                    forall|u: int| 0 <= u && u < j ==> (next[u] as int) < m,
                    forall|u: int| 0 <= u && u < j ==> (next[u] as int) == Self::inv_count(i as int, u),
                    j == 0 ==> window == 0,
                    j > 0 ==> window as int == Self::inv_count(i as int, j as int - 1),
                decreases k - j + 1,
            {
                proof {
                    Self::lemma_inv_count_range(i as int, j as int - 1);
                    Self::lemma_inv_count_range((i - 1) as int, j as int);
                    if j - i >= 0 {
                        Self::lemma_inv_count_range((i - 1) as int, (j - i) as int);
                    }
                }
                assert(0 <= j < dp.len() as i32);
                window += dp[j as usize] as i64;
                if j - i >= 0 {
                    assert(0 <= j - i);
                    assert((j - i) < dp.len() as i32);
                    window -= dp[(j - i) as usize] as i64;
                }
                proof {
                    if j == 0 {
                        assert(window as int == Self::inv_count((i - 1) as int, j as int));
                    } else if j - i < 0 {
                        Self::lemma_window_step_no_sub(i as int, j as int);
                        assert(window as int
                            == Self::inv_count(i as int, j as int - 1) + Self::inv_count((i - 1) as int, j as int));
                        assert(-(m as int) < (window as int) && (window as int) < 2 * (m as int));
                    } else {
                        Self::lemma_window_step_sub(i as int, j as int);
                        assert(window as int
                            == Self::inv_count(i as int, j as int - 1) + Self::inv_count((i - 1) as int, j as int)
                                - Self::inv_count((i - 1) as int, (j - i) as int));
                        assert(-(m as int) < (window as int) && (window as int) < 2 * (m as int));
                    }
                }
                window = window % m;
                if window < 0 {
                    window += m;
                }
                proof {
                    if j == 0 {
                        assert(window as int == Self::inv_count((i - 1) as int, j as int) % Self::modv());
                        Self::lemma_window_step_zero(i as int);
                        assert(window as int == Self::inv_count(i as int, j as int));
                    } else if j - i < 0 {
                        assert(window as int
                            == (Self::inv_count(i as int, j as int - 1) + Self::inv_count((i - 1) as int, j as int))
                                % Self::modv());
                        assert(window as int == Self::inv_count(i as int, j as int));
                    } else {
                        assert(window as int
                            == (Self::inv_count(i as int, j as int - 1) + Self::inv_count((i - 1) as int, j as int)
                                - Self::inv_count((i - 1) as int, (j - i) as int)) % Self::modv());
                        assert(window as int == Self::inv_count(i as int, j as int));
                    }
                }
                assert(0 <= window < m);
                next[j as usize] = window as i32;
                assert(0 <= (next[j as int] as int));
                assert((next[j as int] as int) < m);
                assert forall|u: int| 0 <= u && u < j + 1 implies (next[u] as int) < m by {
                    if u < j {
                        assert((next[u] as int) < m);
                    } else {
                        assert(u == j);
                    }
                };
                assert(next[j as int] as int == Self::inv_count(i as int, j as int));
                j += 1;
            }

            dp = next;
            i += 1;
        }

        dp[k as usize]
    }
}

}
