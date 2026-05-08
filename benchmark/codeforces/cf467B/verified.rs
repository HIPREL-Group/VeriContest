use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn pow2(n: int) -> int
    recommends
        n >= 0,
    decreases n,
{
    if n <= 0 {
        1
    } else {
        2 * pow2(n - 1)
    }
}

pub open spec fn bits_differ_at(x: int, y: int, j: int) -> bool
    recommends
        j >= 0,
        x >= 0,
        y >= 0,
{
    (x / pow2(j)) % 2 != (y / pow2(j)) % 2
}

pub open spec fn xor_popcount_prefix(x: int, y: int, bits_done: int) -> int
    recommends
        0 <= bits_done,
        x >= 0,
        y >= 0,
    decreases bits_done,
{
    if bits_done <= 0 {
        0
    } else {
        xor_popcount_prefix(x, y, bits_done - 1) + if bits_differ_at(x, y, bits_done - 1) {
            1int
        } else {
            0int
        }
    }
}

pub open spec fn friend_count_prefix(
    armies: Seq<i32>,
    fedor: int,
    n: int,
    k: int,
    end: int,
) -> int
    recommends
        0 <= end <= armies.len(),
        forall|t: int| 0 <= t < end ==> #[trigger] armies[t] as int >= 0,
        fedor >= 0,
    decreases end,
{
    if end <= 0 {
        0
    } else {
        friend_count_prefix(armies, fedor, n, k, end - 1) + if xor_popcount_prefix(armies[end - 1] as int, fedor, n) <= k {
            1int
        } else {
            0int
        }
    }
}

proof fn lemma_pow2_pos(j: int)
    requires
        j >= 0,
    ensures
        pow2(j) >= 1,
    decreases j,
{
    if j == 0 {
        reveal_with_fuel(pow2, 2);
    } else {
        lemma_pow2_pos(j - 1);
        reveal_with_fuel(pow2, 2);
    }
}

proof fn lemma_xor_popcount_prefix_step(x: int, y: int, bd: int)
    requires
        0 <= bd,
        x >= 0,
        y >= 0,
    ensures
        xor_popcount_prefix(x, y, bd + 1) == xor_popcount_prefix(x, y, bd) + if bits_differ_at(x, y, bd) {
            1int
        } else {
            0int
        },
{
    assert(bd + 1 > 0);
    assert(xor_popcount_prefix(x, y, bd + 1) == xor_popcount_prefix(x, y, bd) + if bits_differ_at(x, y, (bd + 1) - 1) {
        1int
    } else {
        0int
    });
    assert((bd + 1) - 1 == bd);
}

proof fn lemma_friend_count_prefix_step(
    armies: Seq<i32>,
    fedor: int,
    n: int,
    k: int,
    end: int,
)
    requires
        0 <= end < armies.len(),
        forall|t: int| 0 <= t <= end ==> #[trigger] armies[t] as int >= 0,
        fedor >= 0,
    ensures
        friend_count_prefix(armies, fedor, n, k, end + 1) == friend_count_prefix(armies, fedor, n, k, end)
            + if xor_popcount_prefix(armies[end] as int, fedor, n) <= k {
            1int
        } else {
            0int
        },
{
    assert(end + 1 > 0);
    assert(friend_count_prefix(armies, fedor, n, k, end + 1) == friend_count_prefix(armies, fedor, n, k, end)
        + if xor_popcount_prefix(armies[(end + 1) - 1] as int, fedor, n) <= k {
        1int
    } else {
        0int
    });
    assert((end + 1) - 1 == end);
}

proof fn lemma_pow2_succ(b: int)
    requires
        b >= 0,
    ensures
        pow2(b + 1) == 2 * pow2(b),
{
    reveal_with_fuel(pow2, 2);
}

proof fn lemma_div_halve_step(x: int, b: int)
    requires
        x >= 0,
        0 <= b <= 20,
    ensures
        (x / pow2(b)) / 2 == x / pow2(b + 1),
{
    lemma_pow2_pos(b);
    lemma_pow2_succ(b);
    assert(pow2(b + 1) == 2 * pow2(b));
    assert((x / pow2(b)) / 2 == x / pow2(b + 1)) by (nonlinear_arith)
        requires
            x >= 0,
            pow2(b) >= 1,
            pow2(b + 1) == 2 * pow2(b);
}

proof fn lemma_pow2_mono(a: int, b: int)
    requires
        0 <= a <= b <= 25,
    ensures
        pow2(a) <= pow2(b),
    decreases b - a,
{
    if a == b {
    } else {
        assert(a < b);
        lemma_pow2_mono(a, b - 1);
        reveal_with_fuel(pow2, 2);
        assert(pow2(b) == 2 * pow2(b - 1));
        lemma_pow2_pos(b - 1);
        assert(pow2(b - 1) >= 1);
        assert(pow2(b) >= pow2(b - 1));
    }
}

proof fn lemma_pow2_at_most_1048576(n: int)
    requires
        0 <= n <= 20,
    ensures
        pow2(n) <= 1048576,
{
    reveal_with_fuel(pow2, 25);
    assert(pow2(20) == 1048576);
    lemma_pow2_mono(n, 20);
}

proof fn lemma_bits_differ_from_remainders(xr: i32, yr: i32, x0: int, y0: int, b: int)
    requires
        0 <= b <= 20,
        xr as int == x0 / pow2(b),
        yr as int == y0 / pow2(b),
        x0 >= 0,
        y0 >= 0,
    ensures
        bits_differ_at(x0, y0, b) == ((xr % 2) != (yr % 2)),
{
    lemma_pow2_pos(b);
    assert((xr as int) == x0 / pow2(b));
    assert((yr as int) == y0 / pow2(b));
    assert((x0 / pow2(b)) % 2 == (xr as int) % 2);
    assert((y0 / pow2(b)) % 2 == (yr as int) % 2);
}

impl Solution {
    fn xor_popcount_n(x: i32, y: i32, n_bits: i32) -> (c: i32)
        requires
            0 <= n_bits <= 20,
            0 <= x < 1048576,
            0 <= y < 1048576,
        ensures
            c as int == xor_popcount_prefix(x as int, y as int, n_bits as int),
    {
        let mut c: i32 = 0;
        let mut b: i32 = 0;
        let mut xr: i32 = x;
        let mut yr: i32 = y;
        while b < n_bits
            invariant
                0 <= b <= n_bits,
                n_bits <= 20,
                0 <= x < 1048576,
                0 <= y < 1048576,
                xr >= 0,
                yr >= 0,
                xr as int == (x as int) / pow2(b as int),
                yr as int == (y as int) / pow2(b as int),
                c as int == xor_popcount_prefix(x as int, y as int, b as int),
                c <= b,
                c <= 20,
            decreases n_bits - b,
        {
            proof {
                lemma_pow2_pos(b as int);
                lemma_xor_popcount_prefix_step(x as int, y as int, b as int);
                lemma_bits_differ_from_remainders(xr, yr, x as int, y as int, b as int);
            }
            let xbit = xr % 2;
            let ybit = yr % 2;
            if xbit != ybit {
                c = c + 1;
                proof {
                    assert(bits_differ_at(x as int, y as int, b as int));
                    assert((c as int) == xor_popcount_prefix(x as int, y as int, b as int + 1));
                }
            } else {
                proof {
                    assert(!bits_differ_at(x as int, y as int, b as int));
                    assert((c as int) == xor_popcount_prefix(x as int, y as int, b as int + 1));
                }
            }
            let old_xr = xr;
            let old_yr = yr;
            xr = old_xr / 2;
            yr = old_yr / 2;
            proof {
                lemma_div_halve_step(x as int, b as int);
                lemma_div_halve_step(y as int, b as int);
                assert((old_xr as int) == (x as int) / pow2(b as int));
                assert((old_yr as int) == (y as int) / pow2(b as int));
                assert((xr as int) == (old_xr as int) / 2);
                assert((yr as int) == (old_yr as int) / 2);
                assert((xr as int) == (x as int) / pow2((b + 1) as int));
                assert((yr as int) == (y as int) / pow2((b + 1) as int));
            }
            b = b + 1;
        }
        proof {
            assert(b == n_bits);
        }
        c
    }

    pub fn count_fedor_friends(n: i32, k: i32, armies: Vec<i32>) -> (res: i32)
        requires
            2 <= armies.len() && armies.len() <= 1001,
            0 <= (n as int) && 1 <= (k as int) && (k as int) <= (n as int) && (n as int) <= 20,
            forall|i: int|
                0 <= i < armies@.len() ==> (1 <= #[trigger] armies@[i] && (armies@[i] as int) < 1048576),
        ensures
            res as int == friend_count_prefix(
                armies@,
                armies@[(armies.len() as int) - 1] as int,
                n as int,
                k as int,
                armies.len() as int - 1,
            ),
    {
        let m = armies.len() - 1;
        let fedor = armies[m];
        let mut cnt: i32 = 0;
        let mut i: usize = 0;
        proof {
            assert((n as int) <= 20);
            assert((armies.len() as int) <= 1001);
            lemma_pow2_at_most_1048576(n as int);
            assert(0 <= (m as int) && (m as int) < armies@.len());
            assert(1 <= #[trigger] armies@[m as int] && (armies@[m as int] as int) < 1048576);
        }
        while i < m
            invariant
                (armies.len() as int) <= 1001,
                0 <= i <= m,
                m == armies.len() - 1,
                m < armies.len(),
                fedor as int == armies@[m as int] as int,
                0 <= (n as int) && (n as int) <= 20,
                0 <= fedor && (fedor as int) < 1048576,
                cnt as int == friend_count_prefix(armies@, fedor as int, n as int, k as int, i as int),
                cnt as int <= i as int,
                cnt <= 1000,
                forall|j: int|
                    0 <= j < armies@.len() ==> (1 <= #[trigger] armies@[j] && (armies@[j] as int) < 1048576),
                forall|t: int| 0 <= t < i ==> #[trigger] armies[t] as int >= 0,
            decreases m - i,
        {
            proof {
                assert((n as int) <= 20);
                assert(0 <= (n as int));
                lemma_pow2_at_most_1048576(n as int);
                let ii = i as int;
                assert((m as int) == armies@.len() as int - 1);
                assert((m as int) <= 1000);
                assert((i as int) < (m as int));
                assert(ii < armies@.len());
                assert(0 <= ii);
                assert(1 <= #[trigger] armies@[ii] && (armies@[ii] as int) < 1048576);
                lemma_friend_count_prefix_step(armies@, fedor as int, n as int, k as int, i as int);
                assert((armies@[ii] as int) < 1048576);
                assert((fedor as int) < 1048576);
                assert(0 <= n && n <= 20);
                assert(cnt as int <= i as int);
                assert((m as int) <= 1000);
                assert(cnt + 1 <= (m as int));
                assert(cnt + 1 <= 1000);
            }
            let d = Self::xor_popcount_n(armies[i], fedor, n);
            if d <= k {
                cnt = cnt + 1;
                proof {
                    assert((cnt as int) == friend_count_prefix(armies@, fedor as int, n as int, k as int, i as int + 1));
                }
            } else {
                proof {
                    assert((cnt as int) == friend_count_prefix(armies@, fedor as int, n as int, k as int, i as int + 1));
                }
            }
            i = i + 1;
        }
        proof {
            assert(i == m);
            assert((m as int) == armies.len() as int - 1);
            assert((cnt as int) == friend_count_prefix(armies@, fedor as int, n as int, k as int, m as int));
        }
        cnt
    }
}

}
