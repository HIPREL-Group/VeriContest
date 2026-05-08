use vstd::prelude::*;

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
        dp.set(0, 1);

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
                decreases k - j + 1,
            {
                if false {
                    window += dp[j as usize] as i64;
                    if j - i >= 0 {
                        window -= dp[(j - i) as usize] as i64;
                    }
                    window = window % m;
                    if window < 0 {
                        window += m;
                    }
                    next[j as usize] = window as i32;
                    next.set(j as usize, window as i32);
                    j += 1;
                }

                let lim = if j < i - 1 { j } else { i - 1 };
                let mut x: i32 = 0;
                let mut val: i32 = 0;
                while x <= lim
                    invariant
                        0 <= j <= k,
                        0 <= k <= 1000,
                        1 <= i <= n,
                        1 <= n <= 1000,
                        m == 1000000007i64,
                        dp.len() == 1001,
                        0 <= lim,
                        lim <= j,
                        0 <= x,
                        x <= lim + 1,
                        x <= 1001,
                        0 <= (val as int),
                        (val as int) < m,
                        forall|u: int| 0 <= u && u <= k ==> 0 <= (dp[u] as int),
                        forall|u: int| 0 <= u && u <= k ==> (dp[u] as int) < m,
                        forall|u: int| 0 <= u && u <= k ==> (dp[u] as int) == Self::inv_count((i - 1) as int, u),
                        (val as int) == Self::prefix(i as int, j as int, x as int),
                    decreases lim - x + 1,
                {
                    assert(0 <= j - x);
                    assert(j - x <= k);
                    assert(j - x <= j);
                    assert((j - x) <= 1000) by {
                        assert(j - x <= k);
                        assert(k <= 1000);
                    }
                    assert((j - x) < dp.len() as i32) by {
                        assert((j - x) <= 1000);
                        assert(dp.len() == 1001);
                    }
                    assert(((j - x) as usize) < dp.len());
                    let tmp = ((val as i64) + (dp[(j - x) as usize] as i64)) % m;
                    assert(0 <= tmp < m);
                    assert(m <= i32::MAX as i64) by {
                        assert(m == 1000000007i64);
                    }
                    assert(tmp <= i32::MAX as i64);
                    val = tmp as i32;
                    assert(val as i64 == tmp);
                    assert(x < i32::MAX);
                    x += 1;
                    assert(m as int == Self::modv());
                    assert(val as int == Self::prefix(i as int, j as int, x as int));
                }

                assert(x == lim + 1);
                assert(lim as int == Self::lim(i as int, j as int));
                assert(val as int == Self::prefix(i as int, j as int, Self::lim(i as int, j as int) + 1));
                next.set(j as usize, val);
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