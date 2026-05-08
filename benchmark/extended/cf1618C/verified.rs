use vstd::prelude::*;
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn spec_max_val() -> int {
        1000000000000000000
    }

    pub open spec fn spec_gcd_nat(a: nat, b: nat) -> nat
        decreases b,
    {
        if b == 0 {
            a
        } else {
            Self::spec_gcd_nat(b, a % b)
        }
    }

    pub open spec fn spec_gcd(a: int, b: int) -> int
        recommends
            0 <= a,
            0 <= b,
    {
        Self::spec_gcd_nat(a as nat, b as nat) as int
    }

    pub open spec fn spec_even_gcd_prefix(a: Seq<i64>, hi: int) -> int
        recommends
            hi % 2 == 0,
            2 <= hi <= a.len() + 1,
            forall|k: int| 0 <= k < a.len() ==> 1 <= #[trigger] a[k] <= Self::spec_max_val(),
        decreases hi,
    {
        if hi <= 2 {
            a[0] as int
        } else {
            Self::spec_gcd(Self::spec_even_gcd_prefix(a, hi - 2), a[hi - 2] as int)
        }
    }

    pub open spec fn spec_odd_gcd_prefix(a: Seq<i64>, hi: int) -> int
        recommends
            hi % 2 == 1,
            3 <= hi <= a.len() + 1,
            forall|k: int| 0 <= k < a.len() ==> 1 <= #[trigger] a[k] <= Self::spec_max_val(),
        decreases hi,
    {
        if hi <= 3 {
            a[1] as int
        } else {
            Self::spec_gcd(Self::spec_odd_gcd_prefix(a, hi - 2), a[hi - 2] as int)
        }
    }

    pub open spec fn spec_gcd_all_even(a: Seq<i64>) -> int
        recommends
            2 <= a.len() <= 100,
            forall|k: int| 0 <= k < a.len() ==> 1 <= #[trigger] a[k] <= Self::spec_max_val(),
    {
        let n = a.len() as int;
        Self::spec_even_gcd_prefix(a, n + n % 2)
    }

    pub open spec fn spec_gcd_all_odd(a: Seq<i64>) -> int
        recommends
            2 <= a.len() <= 100,
            forall|k: int| 0 <= k < a.len() ==> 1 <= #[trigger] a[k] <= Self::spec_max_val(),
    {
        let n = a.len() as int;
        Self::spec_odd_gcd_prefix(a, n + 1 - n % 2)
    }

    pub open spec fn spec_divisible_by(x: int, d: int) -> bool {
        d > 0 && x % d == 0
    }

    pub open spec fn spec_beautiful(seq: Seq<i64>, d: int) -> bool {
        forall|i: int|
            #![trigger seq[i]]
            0 <= i < seq.len() - 1 ==> Self::spec_divisible_by(seq[i] as int, d)
                != Self::spec_divisible_by(seq[i + 1] as int, d)
    }

    pub open spec fn spec_exists_beautiful_d(seq: Seq<i64>) -> bool {
        exists|d: int|
            #![trigger Self::spec_beautiful(seq, d)]
            1 <= d <= Self::spec_max_val() && Self::spec_beautiful(seq, d)
    }

    proof fn lemma_gcd_positive(x: int, y: int)
        requires
            0 <= x,
            0 <= y,
            !(x == 0 && y == 0),
        ensures
            Self::spec_gcd(x, y) > 0,
        decreases y,
    {
        reveal_with_fuel(Solution::spec_gcd_nat, 2);
        if y == 0 {
            assert(x > 0);
            assert(Self::spec_gcd(x, y) == x);
        } else {
            Self::lemma_gcd_positive(y, x % y);
        }
    }

    proof fn lemma_div_transitive(x: int, y: int, z: int)
        requires
            0 <= x,
            y > 0,
            z > 0,
            Self::spec_divisible_by(x, y),
            Self::spec_divisible_by(y, z),
        ensures
            Self::spec_divisible_by(x, z),
    {
        lemma_fundamental_div_mod(x, y);
        assert(x == y * (x / y) + x % y);
        assert(x == y * (x / y));
        lemma_fundamental_div_mod(y, z);
        assert(y == z * (y / z) + y % z);
        assert(y == z * (y / z));
        let k = x / y;
        let m = y / z;
        lemma_mul_is_commutative(k, y);
        assert(y * k == k * y);
        assert(k * (m * z) == k * y);
        lemma_mul_is_associative(k, m, z);
        assert((k * m) * z == k * (m * z));
        assert(x == (k * m) * z);
        lemma_mul_is_commutative(z, k * m);
        assert(x == z * (k * m));
        lemma_mod_multiples_basic(k * m, z);
        assert((z * (k * m)) % z == 0);
        assert(x % z == 0);
    }

    proof fn lemma_linear_combo_divisible(x: int, y: int, g: int)
        requires
            y > 0,
            g > 0,
            Self::spec_divisible_by(y, g),
            Self::spec_divisible_by(x % y, g),
        ensures
            Self::spec_divisible_by(x, g),
    {
        let q = x / y;
        let r = x % y;
        lemma_fundamental_div_mod(x, y);
        assert(x == q * y + r);
        assert(r % g == 0);
        assert(y % g == 0);
        assert((q * y) % g == 0) by {
            lemma_fundamental_div_mod(y, g);
            assert(y == g * (y / g) + y % g);
            assert(y == g * (y / g));
            let m = y / g;
            lemma_mul_is_associative(q, g, m);
            assert(q * (g * m) == (q * g) * m);
            assert(q * y == q * (g * m));
            assert(q * y == (q * g) * m);
            lemma_mul_is_commutative(q, g);
            assert((q * g) * m == (g * q) * m);
            lemma_mul_is_associative(g, q, m);
            assert((g * q) * m == g * (q * m));
            assert(q * y == g * (q * m));
            lemma_mod_multiples_basic(q * m, g);
            assert((g * (q * m)) % g == 0);
        };
        assert((q * y + r) % g == 0) by {
            lemma_mod_adds(q * y, r, g);
            assert((q * y) % g + r % g == (q * y + r) % g + g * (((q * y) % g + r % g) / g));
            assert((q * y) % g == 0);
            assert(r % g == 0);
            assert(((q * y) % g + r % g) < g) by {
                lemma_mod_pos_bound(r, g);
            };
        };
        assert(x % g == 0);
    }

    proof fn lemma_gcd_divides_both(x: int, y: int, g: int)
        requires
            0 <= x,
            0 <= y,
            g == Self::spec_gcd(x, y),
            !(x == 0 && y == 0),
        ensures
            Self::spec_divisible_by(x, g),
            Self::spec_divisible_by(y, g),
        decreases y,
    {
        reveal_with_fuel(Solution::spec_gcd_nat, 2);
        Self::lemma_gcd_positive(x, y);
        if y == 0 {
            assert(g == x);
            assert(x > 0);
            assert(x % g == 0);
            assert(y % g == 0);
        } else {
            assert(g == Self::spec_gcd(y, x % y));
            assert(!(y == 0 && x % y == 0) || (x % y != 0)) by {
                if y > 0 && x % y == 0 {
                } else {
                }
            };
            assert(!(y == 0 && x % y == 0));
            Self::lemma_gcd_divides_both(y, x % y, g);
            assert(Self::spec_divisible_by(y, g));
            assert(Self::spec_divisible_by(x % y, g));
            Self::lemma_linear_combo_divisible(x, y, g);
        }
    }

    proof fn lemma_common_divisor_divides_gcd(x: int, y: int, d: int)
        requires
            0 <= x,
            0 <= y,
            1 <= d <= Self::spec_max_val(),
            Self::spec_divisible_by(x, d),
            Self::spec_divisible_by(y, d),
            !(x == 0 && y == 0),
        ensures
            Self::spec_divisible_by(Self::spec_gcd(x, y), d),
        decreases y,
    {
        reveal_with_fuel(Solution::spec_gcd_nat, 2);
        if y == 0 {
            assert(Self::spec_gcd(x, y) == x);
        } else {
            assert((x % y) % d == 0) by {
                lemma_fundamental_div_mod(x, y);
                lemma_fundamental_div_mod(y, d);
                lemma_fundamental_div_mod(x, d);
                let q = x / y;
                let qy = y / d;
                let qx = x / d;
                assert(x == y * q + x % y);
                assert(y == d * qy);
                assert(x == d * qx);
                lemma_mul_is_associative(d, qy, q);
                assert((d * qy) * q == d * (qy * q));
                assert(y * q == d * (qy * q));
                lemma_mul_is_distributive_sub(d, qx, qy * q);
                assert(d * (qx - qy * q) == d * qx - d * (qy * q));
                assert(x % y == d * (qx - qy * q));
                lemma_mod_multiples_basic(qx - qy * q, d);
            };
            Self::lemma_common_divisor_divides_gcd(y, x % y, d);
        }
    }

    proof fn lemma_even_prefix_divisible_by_self(a: Seq<i64>, hi: int, idx: int)
        requires
            hi % 2 == 0,
            2 <= hi <= a.len() + 1,
            idx % 2 == 0,
            0 <= idx < hi,
            forall|k: int| 0 <= k < a.len() ==> 1 <= #[trigger] a[k] <= Self::spec_max_val(),
        ensures
            Self::spec_divisible_by(a[idx] as int, Self::spec_even_gcd_prefix(a, hi)),
        decreases hi,
    {
        if hi <= 2 {
            assert(idx == 0);
            assert(Self::spec_even_gcd_prefix(a, hi) == a[0] as int);
            assert(a[0] as int >= 1);
            lemma_mod_multiples_basic(1, a[0] as int);
            lemma_mul_basics(a[0] as int);
        } else if idx == hi - 2 {
            Self::lemma_gcd_divides_both(
                Self::spec_even_gcd_prefix(a, hi - 2),
                a[hi - 2] as int,
                Self::spec_even_gcd_prefix(a, hi),
            );
        } else {
            Self::lemma_even_prefix_divisible_by_self(a, hi - 2, idx);
            let gp = Self::spec_even_gcd_prefix(a, hi - 2);
            let g = Self::spec_even_gcd_prefix(a, hi);
            Self::lemma_gcd_divides_both(gp, a[hi - 2] as int, g);
            assert(Self::spec_divisible_by(gp, g));
            Self::lemma_div_transitive(a[idx] as int, gp, g);
        }
    }

    proof fn lemma_odd_prefix_divisible_by_self(a: Seq<i64>, hi: int, idx: int)
        requires
            hi % 2 == 1,
            3 <= hi <= a.len() + 1,
            idx % 2 == 1,
            1 <= idx < hi,
            forall|k: int| 0 <= k < a.len() ==> 1 <= #[trigger] a[k] <= Self::spec_max_val(),
        ensures
            Self::spec_divisible_by(a[idx] as int, Self::spec_odd_gcd_prefix(a, hi)),
        decreases hi,
    {
        if hi <= 3 {
            assert(idx == 1);
        } else if idx == hi - 2 {
            Self::lemma_gcd_divides_both(
                Self::spec_odd_gcd_prefix(a, hi - 2),
                a[hi - 2] as int,
                Self::spec_odd_gcd_prefix(a, hi),
            );
        } else {
            Self::lemma_odd_prefix_divisible_by_self(a, hi - 2, idx);
            let gp = Self::spec_odd_gcd_prefix(a, hi - 2);
            let g = Self::spec_odd_gcd_prefix(a, hi);
            Self::lemma_gcd_divides_both(gp, a[hi - 2] as int, g);
            assert(Self::spec_divisible_by(gp, g));
            Self::lemma_div_transitive(a[idx] as int, gp, g);
        }
    }

    proof fn lemma_d_divides_even_prefix(a: Seq<i64>, d: int, hi: int)
        requires
            hi % 2 == 0,
            2 <= hi <= a.len() + 1,
            1 <= d <= Self::spec_max_val(),
            forall|k: int| 0 <= k < a.len() ==> 1 <= #[trigger] a[k] <= Self::spec_max_val(),
            forall|idx: int|
                #![trigger a[idx]]
                idx % 2 == 0 && 0 <= idx < hi ==> Self::spec_divisible_by(a[idx] as int, d),
        ensures
            Self::spec_divisible_by(Self::spec_even_gcd_prefix(a, hi), d),
        decreases hi,
    {
        if hi <= 2 {
            assert(Self::spec_even_gcd_prefix(a, hi) == a[0] as int);
        } else {
            Self::lemma_d_divides_even_prefix(a, d, hi - 2);
            Self::lemma_common_divisor_divides_gcd(
                Self::spec_even_gcd_prefix(a, hi - 2),
                a[hi - 2] as int,
                d,
            );
        }
    }

    proof fn lemma_d_divides_odd_prefix(a: Seq<i64>, d: int, hi: int)
        requires
            hi % 2 == 1,
            3 <= hi <= a.len() + 1,
            1 <= d <= Self::spec_max_val(),
            forall|k: int| 0 <= k < a.len() ==> 1 <= #[trigger] a[k] <= Self::spec_max_val(),
            forall|idx: int|
                #![trigger a[idx]]
                idx % 2 == 1 && 1 <= idx < hi ==> Self::spec_divisible_by(a[idx] as int, d),
        ensures
            Self::spec_divisible_by(Self::spec_odd_gcd_prefix(a, hi), d),
        decreases hi,
    {
        if hi <= 3 {
            assert(Self::spec_odd_gcd_prefix(a, hi) == a[1] as int);
        } else {
            Self::lemma_d_divides_odd_prefix(a, d, hi - 2);
            Self::lemma_common_divisor_divides_gcd(
                Self::spec_odd_gcd_prefix(a, hi - 2),
                a[hi - 2] as int,
                d,
            );
        }
    }

    proof fn lemma_same_parity_same_color(seq: Seq<i64>, d: int, i: int)
        requires
            2 <= seq.len(),
            Self::spec_beautiful(seq, d),
            0 <= i < seq.len() - 2,
        ensures
            Self::spec_divisible_by(seq[i] as int, d) == Self::spec_divisible_by(seq[i + 2] as int, d),
    {
        assert(Self::spec_divisible_by(seq[i] as int, d) != Self::spec_divisible_by(seq[i + 1] as int, d));
        assert(Self::spec_divisible_by(seq[i + 1] as int, d) != Self::spec_divisible_by(seq[i + 2] as int, d));
    }

    proof fn lemma_all_evens_same_color(seq: Seq<i64>, d: int, i: int)
        requires
            2 <= seq.len(),
            Self::spec_beautiful(seq, d),
            0 <= i < seq.len(),
            i % 2 == 0,
        ensures
            Self::spec_divisible_by(seq[i] as int, d) == Self::spec_divisible_by(seq[0] as int, d),
        decreases i,
    {
        if i > 0 {
            assert(2 <= i);
            assert(i - 2 < seq.len() - 2);
            Self::lemma_same_parity_same_color(seq, d, i - 2);
            Self::lemma_all_evens_same_color(seq, d, i - 2);
        }
    }

    proof fn lemma_all_odds_same_color(seq: Seq<i64>, d: int, j: int)
        requires
            2 <= seq.len(),
            Self::spec_beautiful(seq, d),
            1 <= j < seq.len(),
            j % 2 == 1,
        ensures
            Self::spec_divisible_by(seq[j] as int, d) == Self::spec_divisible_by(seq[1] as int, d),
        decreases j,
    {
        if j > 1 {
            assert(3 <= j);
            assert(j - 2 < seq.len() - 2);
            Self::lemma_same_parity_same_color(seq, d, j - 2);
            Self::lemma_all_odds_same_color(seq, d, j - 2);
        }
    }

    proof fn lemma_no_beautiful_when_both_fail(
        a: Seq<i64>,
        g_even: int,
        g_odd: int,
        jo: int,
        je: int,
    )
        requires
            2 <= a.len() <= 100,
            forall|k: int| 0 <= k < a.len() ==> 1 <= #[trigger] a[k] <= Self::spec_max_val(),
            g_even == Self::spec_gcd_all_even(a),
            g_odd == Self::spec_gcd_all_odd(a),
            jo % 2 == 1,
            0 <= jo < a.len(),
            Self::spec_divisible_by(a[jo] as int, g_even),
            je % 2 == 0,
            0 <= je < a.len(),
            Self::spec_divisible_by(a[je] as int, g_odd),
        ensures
            !Self::spec_exists_beautiful_d(a),
    {
        assert forall|d: int| !(1 <= d <= Self::spec_max_val() && Self::spec_beautiful(a, d)) by {
            assert forall|d: int| 1 <= d <= Self::spec_max_val() && Self::spec_beautiful(a, d) implies false by {
                if Self::spec_divisible_by(a[0] as int, d) {
                    assert forall|k: int|
                        #![trigger a[k]]
                        0 <= k < a.len() && k % 2 == 0 ==> Self::spec_divisible_by(a[k] as int, d) by {
                        if 0 <= k && k < a.len() && k % 2 == 0 {
                            Self::lemma_all_evens_same_color(a, d, k);
                        }
                    };
                    let hi = a.len() as int + a.len() as int % 2;
                    Self::lemma_d_divides_even_prefix(a, d, hi);
                    assert(Self::spec_gcd_all_even(a) == Self::spec_even_gcd_prefix(a, hi));
                    assert(Self::spec_divisible_by(g_even, d));
                    assert(Self::spec_divisible_by(a[jo] as int, g_even));
                    Self::lemma_div_transitive(a[jo] as int, g_even, d);
                    assert(Self::spec_divisible_by(a[jo] as int, d));
                    assert(Self::spec_divisible_by(a[0] as int, d));
                    assert(Self::spec_divisible_by(a[1] as int, d) != Self::spec_divisible_by(a[0] as int, d));
                    Self::lemma_all_odds_same_color(a, d, jo);
                    assert(Self::spec_divisible_by(a[jo] as int, d) == Self::spec_divisible_by(a[1] as int, d));
                    assert(false);
                } else {
                    assert(Self::spec_divisible_by(a[1] as int, d));
                    assert forall|k: int|
                        #![trigger a[k]]
                        0 <= k < a.len() && k % 2 == 1 ==> Self::spec_divisible_by(a[k] as int, d) by {
                        if 0 <= k && k < a.len() && k % 2 == 1 {
                            Self::lemma_all_odds_same_color(a, d, k);
                        }
                    };
                    let hi = a.len() as int + 1 - a.len() as int % 2;
                    Self::lemma_d_divides_odd_prefix(a, d, hi);
                    assert(Self::spec_gcd_all_odd(a) == Self::spec_odd_gcd_prefix(a, hi));
                    assert(Self::spec_divisible_by(g_odd, d));
                    assert(Self::spec_divisible_by(a[je] as int, g_odd));
                    Self::lemma_div_transitive(a[je] as int, g_odd, d);
                    assert(Self::spec_divisible_by(a[je] as int, d));
                    assert(!Self::spec_divisible_by(a[0] as int, d));
                    Self::lemma_all_evens_same_color(a, d, je);
                    assert(Self::spec_divisible_by(a[je] as int, d) == Self::spec_divisible_by(a[0] as int, d));
                    assert(false);
                }
            };
        };
    }

    pub fn gcd_two(x: i64, y: i64) -> (g: i64)
        requires
            1 <= x <= Self::spec_max_val(),
            1 <= y <= Self::spec_max_val(),
        ensures
            1 <= g <= Self::spec_max_val(),
            g as int == Self::spec_gcd(x as int, y as int),
    {
        let ghost start_x = x as int;
        let ghost start_y = y as int;
        let mut x = x;
        let mut y = y;
        while y != 0
            invariant
                1 <= x <= Self::spec_max_val(),
                0 <= y <= Self::spec_max_val(),
                Self::spec_gcd(x as int, y as int) == Self::spec_gcd(start_x, start_y),
            decreases y,
        {
            let prev_x = x;
            let prev_y = y;
            proof {
                assert(Self::spec_gcd(prev_x as int, prev_y as int) == Self::spec_gcd(
                    prev_y as int,
                    (prev_x % prev_y) as int,
                ));
            }
            let t = x % y;
            x = y;
            y = t;
        }
        proof {
            assert(y == 0);
            assert(Self::spec_gcd(x as int, 0) == x as int);
            assert(x as int == Self::spec_gcd(start_x, start_y));
            assert(1 <= x as int <= Self::spec_max_val());
        }
        x
    }

    pub fn paint_the_array(a: Vec<i64>) -> (r: i64)
        requires
            2 <= a.len() <= 100,
            forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= Self::spec_max_val(),
        ensures
            r == 0 <==> !Self::spec_exists_beautiful_d(a@),
            r != 0 <==> 1 <= r as int <= Self::spec_max_val() && Self::spec_beautiful(a@, r as int),
    {
        let n = a.len();
        let mut g_even = a[0];
        let mut i: usize = 2;
        while i < n
            invariant
                2 <= a.len() <= 100,
                a.len() == n,
                2 <= i <= n + 1,
                i % 2 == 0,
                1 <= g_even <= Self::spec_max_val(),
                forall|k: int| 0 <= k < n ==> 1 <= #[trigger] a[k] <= Self::spec_max_val(),
                g_even as int == Self::spec_even_gcd_prefix(a@, i as int),
            decreases n + 1 - i,
        {
            proof {
                assert(i as int + 2 <= n as int + 1);
            }
            g_even = Self::gcd_two(g_even, a[i]);
            proof {
                assert(g_even as int == Self::spec_gcd(
                    Self::spec_even_gcd_prefix(a@, i as int),
                    a@[i as int] as int,
                ));
                assert(Self::spec_even_gcd_prefix(a@, (i + 2) as int) == Self::spec_gcd(
                    Self::spec_even_gcd_prefix(a@, i as int),
                    a@[i as int] as int,
                ));
            }
            i = i + 2;
        }
        proof {
            assert(i as int == n as int + (n as int % 2));
            assert(g_even as int == Self::spec_gcd_all_even(a@));
        }
        let mut g_odd = a[1];
        let mut i: usize = 3;
        while i < n
            invariant
                2 <= a.len() <= 100,
                a.len() == n,
                3 <= i <= n + 1,
                i % 2 == 1,
                1 <= g_odd <= Self::spec_max_val(),
                forall|k: int| 0 <= k < n ==> 1 <= #[trigger] a[k] <= Self::spec_max_val(),
                g_odd as int == Self::spec_odd_gcd_prefix(a@, i as int),
            decreases n + 1 - i,
        {
            g_odd = Self::gcd_two(g_odd, a[i]);
            proof {
                assert(Self::spec_odd_gcd_prefix(a@, (i + 2) as int) == Self::spec_gcd(
                    Self::spec_odd_gcd_prefix(a@, i as int),
                    a@[i as int] as int,
                ));
            }
            i = i + 2;
        }
        proof {
            assert(i as int == n as int + 1 - n as int % 2);
            assert(g_odd as int == Self::spec_gcd_all_odd(a@));
        }
        let mut ok_a = true;
        let mut wit_bad_odd: usize = 0;
        let mut j: usize = 1;
        while j < n
            invariant
                2 <= a.len() <= 100,
                a.len() == n,
                1 <= j <= n + 1,
                j % 2 == 1,
                1 <= g_even <= Self::spec_max_val(),
                forall|k: int| 0 <= k < n ==> 1 <= #[trigger] a[k] <= Self::spec_max_val(),
                g_even as int == Self::spec_gcd_all_even(a@),
                ok_a ==> (forall|t: int|
                    #![trigger a@[t]]
                    1 <= t < j && t % 2 == 1 ==> !Self::spec_divisible_by(a@[t] as int, g_even as int)),
                !ok_a ==> (wit_bad_odd as int % 2 == 1 && wit_bad_odd < n
                    && Self::spec_divisible_by(a@[wit_bad_odd as int] as int, g_even as int)),
            decreases n + 2 - j,
        {
            if a[j] % g_even == 0 {
                if ok_a {
                    wit_bad_odd = j;
                }
                ok_a = false;
            }
            j = j + 2;
        }
        if ok_a {
            proof {
                assert(j as int >= n as int);
                assert forall|t: int|
                    #![trigger a@[t]]
                    1 <= t < n && t % 2 == 1 ==> !Self::spec_divisible_by(a@[t] as int, g_even as int) by {
                    if 1 <= t && t < n as int && t % 2 == 1 {
                        assert(t < j as int);
                    }
                };
                let hi = n as int + n as int % 2;
                assert forall|ii: int|
                    #![trigger a@[ii]]
                    0 <= ii < n && ii % 2 == 0 ==> Self::spec_divisible_by(a@[ii] as int, g_even as int) by {
                    if 0 <= ii && ii < n as int && ii % 2 == 0 {
                        Self::lemma_even_prefix_divisible_by_self(a@, hi, ii);
                        assert(Self::spec_gcd_all_even(a@) == g_even as int);
                    }
                };
                assert forall|idx: int|
                    #![trigger a@[idx]]
                    0 <= idx < n - 1 ==> Self::spec_divisible_by(a@[idx] as int, g_even as int)
                        != Self::spec_divisible_by(a@[idx + 1] as int, g_even as int) by {
                    if 0 <= idx && idx < n as int - 1 {
                        if idx % 2 == 0 {
                            assert(Self::spec_divisible_by(a@[idx] as int, g_even as int));
                            assert(1 <= idx + 1 && (idx + 1) % 2 == 1 && idx + 1 < n as int);
                            assert(idx + 1 < j as int);
                            assert(!Self::spec_divisible_by(a@[idx + 1] as int, g_even as int));
                        } else {
                            assert(0 <= idx && idx % 2 == 1 && idx < n as int);
                            assert(idx < j as int);
                            assert(!Self::spec_divisible_by(a@[idx] as int, g_even as int));
                            assert(Self::spec_divisible_by(a@[idx + 1] as int, g_even as int));
                        }
                    }
                };
                assert(Self::spec_beautiful(a@, g_even as int));
            }
            return g_even;
        }
        let mut ok_b = true;
        let mut wit_bad_even: usize = 0;
        let mut j: usize = 0;
        while j < n
            invariant
                2 <= a.len() <= 100,
                a.len() == n,
                j <= n + 1,
                j % 2 == 0,
                1 <= g_odd <= Self::spec_max_val(),
                forall|k: int| 0 <= k < n ==> 1 <= #[trigger] a[k] <= Self::spec_max_val(),
                g_odd as int == Self::spec_gcd_all_odd(a@),
                ok_b ==> (forall|t: int|
                    #![trigger a@[t]]
                    0 <= t < j && t % 2 == 0 ==> !Self::spec_divisible_by(a@[t] as int, g_odd as int)),
                !ok_b ==> (wit_bad_even as int % 2 == 0 && wit_bad_even < n
                    && Self::spec_divisible_by(a@[wit_bad_even as int] as int, g_odd as int)),
            decreases n + 2 - j,
        {
            if a[j] % g_odd == 0 {
                if ok_b {
                    wit_bad_even = j;
                }
                ok_b = false;
            }
            j = j + 2;
        }
        if ok_b {
            proof {
                assert(j as int >= n as int);
                let hi = n as int + 1 - n as int % 2;
                assert forall|ii: int|
                    #![trigger a@[ii]]
                    0 <= ii < n && ii % 2 == 1 ==> Self::spec_divisible_by(a@[ii] as int, g_odd as int) by {
                    if 0 <= ii && ii < n as int && ii % 2 == 1 {
                        Self::lemma_odd_prefix_divisible_by_self(a@, hi, ii);
                        assert(Self::spec_gcd_all_odd(a@) == g_odd as int);
                    }
                };
                assert forall|idx: int|
                    #![trigger a@[idx]]
                    0 <= idx < n - 1 ==> Self::spec_divisible_by(a@[idx] as int, g_odd as int)
                        != Self::spec_divisible_by(a@[idx + 1] as int, g_odd as int) by {
                    if 0 <= idx && idx < n as int - 1 {
                        if idx % 2 == 1 {
                            assert(Self::spec_divisible_by(a@[idx] as int, g_odd as int));
                            assert(idx + 1 < n as int);
                            assert((idx + 1) % 2 == 0);
                            assert(idx + 1 < j as int);
                            assert(!Self::spec_divisible_by(a@[idx + 1] as int, g_odd as int));
                        } else {
                            assert(0 <= idx && idx % 2 == 0 && idx < n as int);
                            assert(idx < j as int);
                            assert(!Self::spec_divisible_by(a@[idx] as int, g_odd as int));
                            assert(Self::spec_divisible_by(a@[idx + 1] as int, g_odd as int));
                        }
                    }
                };
                assert(Self::spec_beautiful(a@, g_odd as int));
            }
            return g_odd;
        }
        proof {
            assert(!ok_a);
            assert(!ok_b);
            assert(wit_bad_odd as int % 2 == 1);
            assert(wit_bad_odd < n);
            assert(Self::spec_divisible_by(a@[wit_bad_odd as int] as int, g_even as int));
            assert(wit_bad_even as int % 2 == 0);
            assert(wit_bad_even < n);
            assert(Self::spec_divisible_by(a@[wit_bad_even as int] as int, g_odd as int));
            Self::lemma_no_beautiful_when_both_fail(
                a@,
                g_even as int,
                g_odd as int,
                wit_bad_odd as int,
                wit_bad_even as int,
            );
        }
        0
    }
}

}
