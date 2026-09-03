use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn fraction_less(s: Seq<i32>, a: int, b: int, num_idx: int, den_idx: int) -> bool {
        (s[a] as int) * (s[den_idx] as int) < (s[num_idx] as int) * (s[b] as int)
    }

    pub open spec fn count_less_inner(s: Seq<i32>, num_idx: int, den_idx: int, a: int, b: int) -> nat
        decreases (s.len() - b) as nat
    {
        if b >= s.len() {
            0nat
        } else if a >= b {
            0nat
        } else {
            let add = if Self::fraction_less(s, a, b, num_idx, den_idx) { 1nat } else { 0nat };
            add + Self::count_less_inner(s, num_idx, den_idx, a, b + 1)
        }
    }

    pub open spec fn count_less_outer(s: Seq<i32>, num_idx: int, den_idx: int, a: int) -> nat
        decreases (s.len() - a) as nat
    {
        if a >= s.len() {
            0nat
        } else {
            Self::count_less_inner(s, num_idx, den_idx, a, a + 1)
                + Self::count_less_outer(s, num_idx, den_idx, a + 1)
        }
    }

    pub open spec fn count_fractions_less(s: Seq<i32>, num_idx: int, den_idx: int) -> nat {
        Self::count_less_outer(s, num_idx, den_idx, 0)
    }

    pub open spec fn is_prime(n: int) -> bool {
        n >= 2 && forall|d: int| 2 <= d < n ==> #[trigger](n % d) != 0
    }

    pub open spec fn count_less_inner_nb(s: Seq<i32>, num_idx: int, den_idx: int, a: int, b: int, nb: int) -> nat
        decreases (nb - b) as nat
    {
        if b >= nb {
            0nat
        } else if a >= b {
            0nat
        } else {
            let add = if Self::fraction_less(s, a, b, num_idx, den_idx) { 1nat } else { 0nat };
            add + Self::count_less_inner_nb(s, num_idx, den_idx, a, b + 1, nb)
        }
    }

    pub open spec fn count_less_outer_nb(s: Seq<i32>, num_idx: int, den_idx: int, a: int, nb: int) -> nat
        decreases (nb - a) as nat
    {
        if a >= nb {
            0nat
        } else {
            Self::count_less_inner_nb(s, num_idx, den_idx, a, a + 1, nb)
                + Self::count_less_outer_nb(s, num_idx, den_idx, a + 1, nb)
        }
    }

    proof fn lemma_inner_nb_eq(s: Seq<i32>, num_idx: int, den_idx: int, a: int, b: int)
        requires
            0 <= a < b,
            b <= s.len(),
        ensures
            Self::count_less_inner_nb(s, num_idx, den_idx, a, b, s.len() as int)
                == Self::count_less_inner(s, num_idx, den_idx, a, b),
        decreases s.len() - b,
    {
        if b < s.len() {
            Self::lemma_inner_nb_eq(s, num_idx, den_idx, a, b + 1);
        }
    }

    proof fn lemma_outer_nb_eq(s: Seq<i32>, num_idx: int, den_idx: int, a: int)
        requires
            0 <= a <= s.len(),
        ensures
            Self::count_less_outer_nb(s, num_idx, den_idx, a, s.len() as int)
                == Self::count_less_outer(s, num_idx, den_idx, a),
        decreases s.len() - a,
    {
        if a < s.len() {
            Self::lemma_inner_nb_eq(s, num_idx, den_idx, a, a + 1);
            Self::lemma_outer_nb_eq(s, num_idx, den_idx, a + 1);
        }
    }

    pub open spec fn count_col_less_from(s: Seq<i32>, a: int, j: int, num_idx: int, den_idx: int) -> nat
        decreases j - a
    {
        if a >= j {
            0nat
        } else {
            let add = if Self::fraction_less(s, a, j, num_idx, den_idx) { 1nat } else { 0nat };
            add + Self::count_col_less_from(s, a + 1, j, num_idx, den_idx)
        }
    }

    pub open spec fn count_col_less(s: Seq<i32>, j: int, num_idx: int, den_idx: int) -> nat {
        Self::count_col_less_from(s, 0, j, num_idx, den_idx)
    }

    pub open spec fn count_cols_upto(s: Seq<i32>, num_idx: int, den_idx: int, big_j: int) -> nat
        decreases big_j
    {
        if big_j <= 0 {
            0nat
        } else {
            Self::count_col_less(s, big_j - 1, num_idx, den_idx) + Self::count_cols_upto(s, num_idx, den_idx, big_j - 1)
        }
    }

    proof fn lemma_inner_nb_extend(s: Seq<i32>, num_idx: int, den_idx: int, a: int, b: int, nb: int)
        requires
            0 <= a,
            a < b,
            b <= nb,
            a < nb,
        ensures
            Self::count_less_inner_nb(s, num_idx, den_idx, a, b, nb + 1)
                == Self::count_less_inner_nb(s, num_idx, den_idx, a, b, nb)
                    + (if Self::fraction_less(s, a, nb, num_idx, den_idx) { 1nat } else { 0nat }),
        decreases nb - b,
    {
        if b < nb {
            Self::lemma_inner_nb_extend(s, num_idx, den_idx, a, b + 1, nb);
            assert(Self::count_less_inner_nb(s, num_idx, den_idx, a, b, nb + 1)
                == (if Self::fraction_less(s, a, b, num_idx, den_idx) { 1nat } else { 0nat })
                    + Self::count_less_inner_nb(s, num_idx, den_idx, a, b + 1, nb + 1));
            assert(Self::count_less_inner_nb(s, num_idx, den_idx, a, b, nb)
                == (if Self::fraction_less(s, a, b, num_idx, den_idx) { 1nat } else { 0nat })
                    + Self::count_less_inner_nb(s, num_idx, den_idx, a, b + 1, nb));
        } else {
            assert(Self::count_less_inner_nb(s, num_idx, den_idx, a, b, nb) == 0nat);
            assert(Self::count_less_inner_nb(s, num_idx, den_idx, a, b, nb + 1)
                == (if Self::fraction_less(s, a, b, num_idx, den_idx) { 1nat } else { 0nat })
                    + Self::count_less_inner_nb(s, num_idx, den_idx, a, b + 1, nb + 1));
            assert(Self::count_less_inner_nb(s, num_idx, den_idx, a, b + 1, nb + 1) == 0nat);
        }
    }

    proof fn lemma_outer_nb_extend(s: Seq<i32>, num_idx: int, den_idx: int, a: int, nb: int)
        requires
            0 <= a <= nb,
        ensures
            Self::count_less_outer_nb(s, num_idx, den_idx, a, nb + 1)
                == Self::count_less_outer_nb(s, num_idx, den_idx, a, nb)
                    + Self::count_col_less_from(s, a, nb, num_idx, den_idx),
        decreases nb - a,
    {
        if a == nb {
            assert(Self::count_less_outer_nb(s, num_idx, den_idx, a, nb + 1)
                == Self::count_less_inner_nb(s, num_idx, den_idx, a, a + 1, nb + 1)
                    + Self::count_less_outer_nb(s, num_idx, den_idx, a + 1, nb + 1));
            assert(Self::count_less_inner_nb(s, num_idx, den_idx, a, a + 1, nb + 1) == 0nat);
            assert(Self::count_less_outer_nb(s, num_idx, den_idx, a + 1, nb + 1) == 0nat);
            assert(Self::count_less_outer_nb(s, num_idx, den_idx, a, nb) == 0nat);
            assert(Self::count_col_less_from(s, a, nb, num_idx, den_idx) == 0nat);
        } else {
            Self::lemma_outer_nb_extend(s, num_idx, den_idx, a + 1, nb);
            Self::lemma_inner_nb_extend(s, num_idx, den_idx, a, a + 1, nb);
            assert(Self::count_less_outer_nb(s, num_idx, den_idx, a, nb + 1)
                == Self::count_less_inner_nb(s, num_idx, den_idx, a, a + 1, nb + 1)
                    + Self::count_less_outer_nb(s, num_idx, den_idx, a + 1, nb + 1));
            assert(Self::count_less_outer_nb(s, num_idx, den_idx, a, nb)
                == Self::count_less_inner_nb(s, num_idx, den_idx, a, a + 1, nb)
                    + Self::count_less_outer_nb(s, num_idx, den_idx, a + 1, nb));
            assert(Self::count_col_less_from(s, a, nb, num_idx, den_idx)
                == (if Self::fraction_less(s, a, nb, num_idx, den_idx) { 1nat } else { 0nat })
                    + Self::count_col_less_from(s, a + 1, nb, num_idx, den_idx));
        }
    }

    proof fn lemma_reorder_step(s: Seq<i32>, num_idx: int, den_idx: int, nb: int)
        requires
            nb >= 0,
        ensures
            Self::count_less_outer_nb(s, num_idx, den_idx, 0, nb + 1)
                == Self::count_less_outer_nb(s, num_idx, den_idx, 0, nb)
                    + Self::count_col_less(s, nb, num_idx, den_idx),
    {
        Self::lemma_outer_nb_extend(s, num_idx, den_idx, 0, nb);
    }

    proof fn lemma_reorder(s: Seq<i32>, num_idx: int, den_idx: int, big_j: int)
        requires
            big_j >= 0,
        ensures
            Self::count_less_outer_nb(s, num_idx, den_idx, 0, big_j) == Self::count_cols_upto(s, num_idx, den_idx, big_j),
        decreases big_j,
    {
        if big_j > 0 {
            Self::lemma_reorder(s, num_idx, den_idx, big_j - 1);
            Self::lemma_reorder_step(s, num_idx, den_idx, big_j - 1);
        }
    }

    proof fn lemma_count_fractions_less_col(s: Seq<i32>, num_idx: int, den_idx: int)
        ensures
            Self::count_fractions_less(s, num_idx, den_idx) == Self::count_cols_upto(s, num_idx, den_idx, s.len() as int),
    {
        Self::lemma_outer_nb_eq(s, num_idx, den_idx, 0);
        Self::lemma_reorder(s, num_idx, den_idx, s.len() as int);
    }


    pub open spec fn spec_gcd(a: nat, b: nat) -> nat
        decreases b,
    {
        if b == 0 { a } else { Self::spec_gcd(b, (a % b) as nat) }
    }

    proof fn lemma_gcd_divides(a: nat, b: nat)
        ensures
            exists|k: int| 0 <= k && a as int == #[trigger] (k * Self::spec_gcd(a, b) as int),
            exists|k: int| 0 <= k && b as int == #[trigger] (k * Self::spec_gcd(a, b) as int),
        decreases b,
    {
        if b == 0 {
            assert(a as int == 1 * Self::spec_gcd(a, b) as int);
            assert(b as int == 0 * Self::spec_gcd(a, b) as int);
        } else {
            Self::lemma_gcd_divides(b, (a % b) as nat);
            let g = Self::spec_gcd(b, (a % b) as nat);
            assert(Self::spec_gcd(a, b) == g);
            let k1 = choose|k: int| 0 <= k && b as int == #[trigger] (k * g as int);
            let k2 = choose|k: int| 0 <= k && (a % b) as int == #[trigger] (k * g as int);
            assert(a as int == (a / b) as int * (b as int) + (a % b) as int) by (nonlinear_arith)
                requires
                    b > 0,
            {
            }
            assert(a as int == (a / b) as int * (k1 * g as int) + k2 * g as int);
            assert(a as int == ((a / b) as int * k1 + k2) * g as int) by (nonlinear_arith)
                requires
                    a as int == (a / b) as int * (k1 * g as int) + k2 * g as int,
            {
            }
            assert((a / b) as int * k1 + k2 >= 0);
        }
    }

    proof fn lemma_gcd_pos(a: nat, b: nat)
        requires
            a >= 1,
        ensures
            Self::spec_gcd(a, b) >= 1,
        decreases b,
    {
        if b == 0 {
        } else {
            if a % b == 0 {
                assert(Self::spec_gcd(a, b) == Self::spec_gcd(b, 0nat));
                assert(Self::spec_gcd(b, 0nat) == b);
                assert(b >= 1);
            } else {
                Self::lemma_gcd_pos(b, (a % b) as nat);
            }
        }
    }

    proof fn lemma_gcd_prime(p: int, x: int)
        requires
            Self::is_prime(p),
            1 <= x < p,
        ensures
            Self::spec_gcd(p as nat, x as nat) == 1,
    {
        Self::lemma_gcd_divides(p as nat, x as nat);
        Self::lemma_gcd_pos(p as nat, x as nat);
        let g = Self::spec_gcd(p as nat, x as nat);
        let k = choose|k: int| 0 <= k && p as int == #[trigger] (k * g as int);
        let k2 = choose|k2: int| 0 <= k2 && x as int == #[trigger] (k2 * g as int);
        assert(g >= 1);
        assert(k2 >= 1) by (nonlinear_arith)
            requires
                x as int == k2 * g as int,
                x >= 1,
                g as int >= 1,
        {
        }
        assert(g as int <= x as int) by (nonlinear_arith)
            requires
                x as int == k2 * g as int,
                k2 >= 1,
                g as int >= 1,
        {
        }
        if g >= 2 {
            assert(1 <= (g as int) < p);
            assert(p % (g as int) == 0) by (nonlinear_arith)
                requires
                    p == k * (g as int),
                    g >= 2,
            {
            }
            assert(false);
        }
    }

    proof fn lemma_bezout(a: nat, b: nat) -> (uv: (int, int))
        ensures
            uv.0 * (a as int) + uv.1 * (b as int) == Self::spec_gcd(a, b) as int,
        decreases b,
    {
        if b == 0 {
            (1, 0)
        } else {
            let uv2 = Self::lemma_bezout(b, (a % b) as nat);
            let (u2, v2) = uv2;
            assert(u2 * (b as int) + v2 * ((a % b) as int) == Self::spec_gcd(b, (a % b) as nat) as int);
            assert(Self::spec_gcd(a, b) == Self::spec_gcd(b, (a % b) as nat));
            assert(a as int == (a / b) as int * (b as int) + (a % b) as int) by (nonlinear_arith)
                requires
                    b > 0,
            {
            }
            let new_u = v2;
            let new_v = u2 - v2 * ((a / b) as int);
            assert(new_u * (a as int) + new_v * (b as int) == Self::spec_gcd(a, b) as int) by (nonlinear_arith)
                requires
                    a as int == (a / b) as int * (b as int) + (a % b) as int,
                    u2 * (b as int) + v2 * ((a % b) as int) == Self::spec_gcd(a, b) as int,
                    new_u == v2,
                    new_v == u2 - v2 * ((a / b) as int),
            {
            }
            (new_u, new_v)
        }
    }

    proof fn lemma_distinct_prime_fractions(p: int, q: int, x: int, y: int)
        requires
            Self::is_prime(p),
            Self::is_prime(q),
            p != q,
            1 <= x < p,
            1 <= y < q,
        ensures
            x * q != y * p,
    {
        if x * q == y * p {
            Self::lemma_gcd_prime(p, x);
            let uv = Self::lemma_bezout(p as nat, x as nat);
            let (u, v) = uv;
            assert(u * (p as int) + v * (x as int) == 1);
            assert(u * (p as int) * (q as int) + v * (x as int) * (q as int) == q as int) by (nonlinear_arith)
                requires
                    u * (p as int) + v * (x as int) == 1,
            {
            }
            assert(v * (x as int * q as int) == v * (y as int * p as int)) by (nonlinear_arith)
                requires
                    x * q == y * p,
            {
            }
            assert(u * (p as int) * (q as int) + v * (y as int) * (p as int) == q as int) by (nonlinear_arith)
                requires
                    u * (p as int) * (q as int) + v * (x as int) * (q as int) == q as int,
                    v * (x as int * q as int) == v * (y as int * p as int),
            {
            }
            assert(q as int == (u * (q as int) + v * (y as int)) * (p as int)) by (nonlinear_arith)
                requires
                    u * (p as int) * (q as int) + v * (y as int) * (p as int) == q as int,
            {
            }
            let m = u * (q as int) + v * (y as int);
            assert(q as int == m * (p as int));
            assert(q % p == 0) by (nonlinear_arith)
                requires
                    q as int == m * (p as int),
                    p >= 2,
            {
            }
            assert(p >= 2);
            if p < q {
                assert(Self::is_prime(q));
                assert(2 <= p < q ==> #[trigger](q % p) != 0);
                assert(false);
            } else {
                assert(p > q);
                assert(q >= 2);
                assert(m <= 0) by (nonlinear_arith)
                    requires
                        m * (p as int) == q as int,
                        p > q,
                        q >= 2,
                {
                }
                assert(m * (p as int) <= 0) by (nonlinear_arith)
                    requires
                        m <= 0,
                        p >= 2,
                {
                }
                assert(false);
            }
        }
    }

    proof fn lemma_fractions_distinct(s: Seq<i32>, j1: int, a1: int, j2: int, a2: int)
        requires
            s[0] == 1,
            forall|i: int| 0 <= i < s.len() ==> 1 <= #[trigger] s[i] <= 30_000,
            forall|i: int| 1 <= i < s.len() ==> #[trigger] Self::is_prime(s[i] as int),
            forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] < s[j],
            1 <= j1 < s.len(),
            1 <= j2 < s.len(),
            j1 != j2,
            0 <= a1 < j1,
            0 <= a2 < j2,
        ensures
            (s[a1] as int) * (s[j2] as int) != (s[a2] as int) * (s[j1] as int),
    {
        Self::lemma_distinct_prime_fractions(s[j1] as int, s[j2] as int, s[a1] as int, s[a2] as int);
    }

    proof fn lemma_count_col_less_threshold_from(s: Seq<i32>, a0: int, j: int, num_idx: int, den_idx: int, t: int)
        requires
            0 <= a0 <= j,
            0 <= t <= j,
            forall|a: int| a0 <= a < t ==> #[trigger] Self::fraction_less(s, a, j, num_idx, den_idx),
            forall|a: int| t <= a < j ==> !#[trigger] Self::fraction_less(s, a, j, num_idx, den_idx),
        ensures
            Self::count_col_less_from(s, a0, j, num_idx, den_idx)
                == (if t > a0 { (t - a0) as nat } else { 0nat }),
        decreases j - a0,
    {
        if a0 < j {
            Self::lemma_count_col_less_threshold_from(s, a0 + 1, j, num_idx, den_idx, t);
            if a0 < t {
                assert(Self::fraction_less(s, a0, j, num_idx, den_idx));
            } else {
                assert(!Self::fraction_less(s, a0, j, num_idx, den_idx));
            }
            assert(Self::count_col_less_from(s, a0, j, num_idx, den_idx)
                == (if Self::fraction_less(s, a0, j, num_idx, den_idx) { 1nat } else { 0nat })
                    + Self::count_col_less_from(s, a0 + 1, j, num_idx, den_idx));
        }
    }

    proof fn lemma_count_col_less_threshold(s: Seq<i32>, j: int, num_idx: int, den_idx: int, t: int)
        requires
            0 <= t <= j,
            forall|a: int| 0 <= a < t ==> #[trigger] Self::fraction_less(s, a, j, num_idx, den_idx),
            forall|a: int| t <= a < j ==> !#[trigger] Self::fraction_less(s, a, j, num_idx, den_idx),
        ensures
            Self::count_col_less(s, j, num_idx, den_idx) == t as nat,
    {
        Self::lemma_count_col_less_threshold_from(s, 0, j, num_idx, den_idx, t);
    }

    proof fn lemma_count_col_less_self(s: Seq<i32>, j: int, i: int)
        requires
            forall|a: int, b: int| 0 <= a < b < s.len() ==> s[a] < s[b],
            forall|a: int| 0 <= a < s.len() ==> 1 <= #[trigger] s[a],
            0 <= i < j < s.len(),
        ensures
            Self::count_col_less(s, j, i, j) == i as nat,
    {
        assert forall|a: int| 0 <= a < i implies #[trigger] Self::fraction_less(s, a, j, i, j) by {
            assert(s[a] < s[i]);
            assert((s[a] as int) * (s[j] as int) < (s[i] as int) * (s[j] as int)) by (nonlinear_arith)
                requires
                    s[a] < s[i],
                    s[j] as int >= 1,
            {
            }
        }
        assert forall|a: int| i <= a < j implies !(#[trigger] Self::fraction_less(s, a, j, i, j)) by {
            if a > i {
                assert(s[i] < s[a]);
            }
            assert((s[a] as int) * (s[j] as int) >= (s[i] as int) * (s[j] as int)) by (nonlinear_arith)
                requires
                    s[a] as int >= s[i] as int,
                    s[j] as int >= 1,
            {
            }
        }
        Self::lemma_count_col_less_threshold(s, j, i, j, i);
    }
    pub open spec fn frac_le(s: Seq<i32>, a: int, b: int, num: int, den: int) -> bool {
        (s[a] as int) * den <= num * (s[b] as int)
    }

    pub open spec fn count_le_col_from(s: Seq<i32>, a: int, j: int, num: int, den: int) -> nat
        decreases j - a
    {
        if a >= j {
            0nat
        } else {
            let add = if Self::frac_le(s, a, j, num, den) { 1nat } else { 0nat };
            add + Self::count_le_col_from(s, a + 1, j, num, den)
        }
    }

    pub open spec fn count_le_col(s: Seq<i32>, j: int, num: int, den: int) -> nat {
        Self::count_le_col_from(s, 0, j, num, den)
    }

    pub open spec fn count_le_upto(s: Seq<i32>, num: int, den: int, big_j: int) -> nat
        decreases big_j
    {
        if big_j <= 0 {
            0nat
        } else {
            Self::count_le_col(s, big_j - 1, num, den) + Self::count_le_upto(s, num, den, big_j - 1)
        }
    }

    pub open spec fn count_le(s: Seq<i32>, num: int, den: int) -> nat {
        Self::count_le_upto(s, num, den, s.len() as int)
    }

    proof fn lemma_count_le_col_threshold_from(s: Seq<i32>, a0: int, j: int, num: int, den: int, t: int)
        requires
            0 <= a0 <= j < s.len(),
            0 <= t <= j,
            forall|a: int| a0 <= a < t ==> #[trigger] Self::frac_le(s, a, j, num, den),
            forall|a: int| t <= a < j ==> !#[trigger] Self::frac_le(s, a, j, num, den),
        ensures
            Self::count_le_col_from(s, a0, j, num, den) == (if t > a0 { (t - a0) as nat } else { 0nat }),
        decreases j - a0,
    {
        if a0 < j {
            Self::lemma_count_le_col_threshold_from(s, a0 + 1, j, num, den, t);
            if a0 < t {
                assert(Self::frac_le(s, a0, j, num, den));
            } else {
                assert(!Self::frac_le(s, a0, j, num, den));
            }
            assert(Self::count_le_col_from(s, a0, j, num, den)
                == (if Self::frac_le(s, a0, j, num, den) { 1nat } else { 0nat })
                    + Self::count_le_col_from(s, a0 + 1, j, num, den));
        }
    }

    proof fn lemma_count_le_col_threshold(s: Seq<i32>, j: int, num: int, den: int, t: int)
        requires
            0 <= t <= j < s.len(),
            forall|a: int| 0 <= a < t ==> #[trigger] Self::frac_le(s, a, j, num, den),
            forall|a: int| t <= a < j ==> !#[trigger] Self::frac_le(s, a, j, num, den),
        ensures
            Self::count_le_col(s, j, num, den) == t as nat,
    {
        Self::lemma_count_le_col_threshold_from(s, 0, j, num, den, t);
    }

    proof fn lemma_col_le_vs_less_from(s: Seq<i32>, a0: int, j: int, ans_i: int, ans_j: int)
        requires
            s[0] == 1,
            forall|i: int| 0 <= i < s.len() ==> 1 <= #[trigger] s[i] <= 30_000,
            forall|i: int| 1 <= i < s.len() ==> #[trigger] Self::is_prime(s[i] as int),
            forall|i: int, j2: int| 0 <= i < j2 < s.len() ==> s[i] < s[j2],
            1 <= ans_j < s.len(),
            0 <= ans_i < ans_j,
            1 <= j < s.len(),
            j != ans_j,
            0 <= a0 <= j,
        ensures
            Self::count_le_col_from(s, a0, j, s[ans_i] as int, s[ans_j] as int)
                == Self::count_col_less_from(s, a0, j, ans_i, ans_j),
        decreases j - a0,
    {
        if a0 < j {
            Self::lemma_col_le_vs_less_from(s, a0 + 1, j, ans_i, ans_j);
            if Self::frac_le(s, a0, j, s[ans_i] as int, s[ans_j] as int)
                && !Self::fraction_less(s, a0, j, ans_i, ans_j) {
                assert((s[a0] as int) * (s[ans_j] as int) == (s[ans_i] as int) * (s[j] as int));
                assert(false) by {
                    Self::lemma_fractions_distinct(s, j, a0, ans_j, ans_i);
                }
            }
            if !Self::frac_le(s, a0, j, s[ans_i] as int, s[ans_j] as int)
                && Self::fraction_less(s, a0, j, ans_i, ans_j) {
                assert(false);
            }
        }
    }

    proof fn lemma_col_le_vs_less(s: Seq<i32>, j: int, ans_i: int, ans_j: int)
        requires
            s[0] == 1,
            forall|i: int| 0 <= i < s.len() ==> 1 <= #[trigger] s[i] <= 30_000,
            forall|i: int| 1 <= i < s.len() ==> #[trigger] Self::is_prime(s[i] as int),
            forall|i: int, j2: int| 0 <= i < j2 < s.len() ==> s[i] < s[j2],
            1 <= ans_j < s.len(),
            0 <= ans_i < ans_j,
            1 <= j < s.len(),
            j != ans_j,
        ensures
            Self::count_le_col(s, j, s[ans_i] as int, s[ans_j] as int) == Self::count_col_less(s, j, ans_i, ans_j),
    {
        Self::lemma_col_le_vs_less_from(s, 0, j, ans_i, ans_j);
    }

    proof fn lemma_col_le_self(s: Seq<i32>, ans_i: int, ans_j: int)
        requires
            forall|i: int| 0 <= i < s.len() ==> 1 <= #[trigger] s[i],
            forall|i: int, j2: int| 0 <= i < j2 < s.len() ==> s[i] < s[j2],
            1 <= ans_j < s.len(),
            0 <= ans_i < ans_j,
        ensures
            Self::count_le_col(s, ans_j, s[ans_i] as int, s[ans_j] as int) == (ans_i + 1) as nat,
    {
        assert forall|a: int| 0 <= a < ans_i + 1 implies
            #[trigger] Self::frac_le(s, a, ans_j, s[ans_i] as int, s[ans_j] as int) by {
            if a < ans_i {
                assert(s[a] < s[ans_i]);
            }
            assert((s[a] as int) * (s[ans_j] as int) <= (s[ans_i] as int) * (s[ans_j] as int)) by (nonlinear_arith)
                requires
                    s[a] as int <= s[ans_i] as int,
                    s[ans_j] as int >= 1,
            {
            }
        }
        assert forall|a: int| ans_i + 1 <= a < ans_j implies
            !(#[trigger] Self::frac_le(s, a, ans_j, s[ans_i] as int, s[ans_j] as int)) by {
            assert(s[ans_i] < s[a]);
            assert((s[a] as int) * (s[ans_j] as int) > (s[ans_i] as int) * (s[ans_j] as int)) by (nonlinear_arith)
                requires
                    (s[ans_i] as int) < (s[a] as int),
                    s[ans_j] as int >= 1,
            {
            }
        }
        Self::lemma_count_le_col_threshold(s, ans_j, s[ans_i] as int, s[ans_j] as int, ans_i + 1);
    }

    proof fn lemma_count_le_exact(s: Seq<i32>, ans_i: int, ans_j: int)
        requires
            s[0] == 1,
            forall|i: int| 0 <= i < s.len() ==> 1 <= #[trigger] s[i] <= 30_000,
            forall|i: int| 1 <= i < s.len() ==> #[trigger] Self::is_prime(s[i] as int),
            forall|i: int, j2: int| 0 <= i < j2 < s.len() ==> s[i] < s[j2],
            1 <= ans_j < s.len(),
            0 <= ans_i < ans_j,
        ensures
            Self::count_le(s, s[ans_i] as int, s[ans_j] as int)
                == Self::count_fractions_less(s, ans_i, ans_j) + 1,
    {
        Self::lemma_count_fractions_less_col(s, ans_i, ans_j);
        Self::lemma_col_le_self(s, ans_i, ans_j);
        assert forall|j: int| 1 <= j < s.len() && j != ans_j implies
            #[trigger] Self::count_le_col(s, j, s[ans_i] as int, s[ans_j] as int)
                == Self::count_col_less(s, j, ans_i, ans_j) by {
            Self::lemma_col_le_vs_less(s, j, ans_i, ans_j);
        }
        assert(Self::count_le_col(s, 0, s[ans_i] as int, s[ans_j] as int) == 0nat);
        assert(Self::count_col_less(s, 0, ans_i, ans_j) == 0nat);
        Self::lemma_count_le_upto_vs_cols_upto(s, ans_i, ans_j, s.len() as int);
    }

    proof fn lemma_count_le_upto_vs_cols_upto(s: Seq<i32>, ans_i: int, ans_j: int, big_j: int)
        requires
            s[0] == 1,
            forall|i: int| 0 <= i < s.len() ==> 1 <= #[trigger] s[i] <= 30_000,
            forall|i: int| 1 <= i < s.len() ==> #[trigger] Self::is_prime(s[i] as int),
            forall|i: int, j2: int| 0 <= i < j2 < s.len() ==> s[i] < s[j2],
            1 <= ans_j < s.len(),
            0 <= ans_i < ans_j,
            ans_j < big_j <= s.len(),
            Self::count_le_col(s, ans_j, s[ans_i] as int, s[ans_j] as int) == (ans_i + 1) as nat,
            forall|j: int| 1 <= j < s.len() && j != ans_j ==>
                #[trigger] Self::count_le_col(s, j, s[ans_i] as int, s[ans_j] as int)
                    == Self::count_col_less(s, j, ans_i, ans_j),
            Self::count_le_col(s, 0, s[ans_i] as int, s[ans_j] as int) == 0nat,
            Self::count_col_less(s, 0, ans_i, ans_j) == 0nat,
        ensures
            Self::count_le_upto(s, s[ans_i] as int, s[ans_j] as int, big_j)
                == Self::count_cols_upto(s, ans_i, ans_j, big_j) + 1,
        decreases big_j,
    {
        if big_j > ans_j + 1 {
            Self::lemma_count_le_upto_vs_cols_upto(s, ans_i, ans_j, big_j - 1);
            assert(Self::count_le_upto(s, s[ans_i] as int, s[ans_j] as int, big_j)
                == Self::count_le_col(s, big_j - 1, s[ans_i] as int, s[ans_j] as int)
                    + Self::count_le_upto(s, s[ans_i] as int, s[ans_j] as int, big_j - 1));
            assert(Self::count_cols_upto(s, ans_i, ans_j, big_j)
                == Self::count_col_less(s, big_j - 1, ans_i, ans_j)
                    + Self::count_cols_upto(s, ans_i, ans_j, big_j - 1));
            assert(big_j - 1 != ans_j);
            assert(1 <= big_j - 1);
            assert(Self::count_le_col(s, big_j - 1, s[ans_i] as int, s[ans_j] as int)
                == Self::count_col_less(s, big_j - 1, ans_i, ans_j));
        } else {
            assert(big_j == ans_j + 1);
            Self::lemma_count_le_upto_vs_cols_upto_below(s, ans_i, ans_j, ans_j);
            Self::lemma_count_col_less_self(s, ans_j, ans_i);
            assert(Self::count_le_upto(s, s[ans_i] as int, s[ans_j] as int, big_j)
                == Self::count_le_col(s, ans_j, s[ans_i] as int, s[ans_j] as int)
                    + Self::count_le_upto(s, s[ans_i] as int, s[ans_j] as int, ans_j));
            assert(Self::count_cols_upto(s, ans_i, ans_j, big_j)
                == Self::count_col_less(s, ans_j, ans_i, ans_j)
                    + Self::count_cols_upto(s, ans_i, ans_j, ans_j));
        }
    }

    proof fn lemma_count_le_upto_vs_cols_upto_below(s: Seq<i32>, ans_i: int, ans_j: int, big_j: int)
        requires
            s[0] == 1,
            forall|i: int| 0 <= i < s.len() ==> 1 <= #[trigger] s[i] <= 30_000,
            forall|i: int| 1 <= i < s.len() ==> #[trigger] Self::is_prime(s[i] as int),
            forall|i: int, j2: int| 0 <= i < j2 < s.len() ==> s[i] < s[j2],
            1 <= ans_j < s.len(),
            0 <= ans_i < ans_j,
            0 <= big_j <= ans_j,
            forall|j: int| 1 <= j < s.len() && j != ans_j ==>
                #[trigger] Self::count_le_col(s, j, s[ans_i] as int, s[ans_j] as int)
                    == Self::count_col_less(s, j, ans_i, ans_j),
            Self::count_le_col(s, 0, s[ans_i] as int, s[ans_j] as int) == 0nat,
            Self::count_col_less(s, 0, ans_i, ans_j) == 0nat,
        ensures
            Self::count_le_upto(s, s[ans_i] as int, s[ans_j] as int, big_j)
                == Self::count_cols_upto(s, ans_i, ans_j, big_j),
        decreases big_j,
    {
        if big_j > 0 {
            Self::lemma_count_le_upto_vs_cols_upto_below(s, ans_i, ans_j, big_j - 1);
            assert(Self::count_le_upto(s, s[ans_i] as int, s[ans_j] as int, big_j)
                == Self::count_le_col(s, big_j - 1, s[ans_i] as int, s[ans_j] as int)
                    + Self::count_le_upto(s, s[ans_i] as int, s[ans_j] as int, big_j - 1));
            assert(Self::count_cols_upto(s, ans_i, ans_j, big_j)
                == Self::count_col_less(s, big_j - 1, ans_i, ans_j)
                    + Self::count_cols_upto(s, ans_i, ans_j, big_j - 1));
            if big_j - 1 != 0 {
                assert(big_j - 1 != ans_j);
                assert(1 <= big_j - 1);
                assert(Self::count_le_col(s, big_j - 1, s[ans_i] as int, s[ans_j] as int)
                    == Self::count_col_less(s, big_j - 1, ans_i, ans_j));
            }
        }
    }

    proof fn lemma_count_le_col_cross_monotone(s: Seq<i32>, j: int, num1: int, den1: int, num2: int, den2: int)
        requires
            num1 * den2 <= num2 * den1,
            den1 > 0,
            den2 > 0,
            forall|a: int| 0 <= a < s.len() ==> 1 <= #[trigger] s[a],
            0 <= j < s.len(),
        ensures
            Self::count_le_col(s, j, num1, den1) <= Self::count_le_col(s, j, num2, den2),
    {
        Self::lemma_count_le_col_cross_monotone_from(s, 0, j, num1, den1, num2, den2);
    }

    proof fn lemma_count_le_col_cross_monotone_from(s: Seq<i32>, a: int, j: int, num1: int, den1: int, num2: int, den2: int)
        requires
            num1 * den2 <= num2 * den1,
            den1 > 0,
            den2 > 0,
            forall|i: int| 0 <= i < s.len() ==> 1 <= #[trigger] s[i],
            0 <= a <= j < s.len(),
        ensures
            Self::count_le_col_from(s, a, j, num1, den1) <= Self::count_le_col_from(s, a, j, num2, den2),
        decreases j - a,
    {
        if a < j {
            Self::lemma_count_le_col_cross_monotone_from(s, a + 1, j, num1, den1, num2, den2);
            if Self::frac_le(s, a, j, num1, den1) {
                assert((s[a] as int) * den1 * den2 <= num1 * (s[j] as int) * den2) by (nonlinear_arith)
                    requires
                        (s[a] as int) * den1 <= num1 * (s[j] as int),
                        den2 >= 0,
                {
                }
                assert(num1 * (s[j] as int) * den2 <= num2 * (s[j] as int) * den1) by (nonlinear_arith)
                    requires
                        num1 * den2 <= num2 * den1,
                        s[j] as int >= 0,
                {
                }
                assert((s[a] as int) * den1 * den2 <= num2 * (s[j] as int) * den1) by (nonlinear_arith)
                    requires
                        (s[a] as int) * den1 * den2 <= num1 * (s[j] as int) * den2,
                        num1 * (s[j] as int) * den2 <= num2 * (s[j] as int) * den1,
                {
                }
                assert((s[a] as int) * den2 <= num2 * (s[j] as int)) by (nonlinear_arith)
                    requires
                        (s[a] as int) * den1 * den2 <= num2 * (s[j] as int) * den1,
                        den1 > 0,
                {
                }
            }
        }
    }

    proof fn lemma_count_le_upto_cross_monotone(s: Seq<i32>, num1: int, den1: int, num2: int, den2: int, big_j: int)
        requires
            num1 * den2 <= num2 * den1,
            den1 > 0,
            den2 > 0,
            forall|a: int| 0 <= a < s.len() ==> 1 <= #[trigger] s[a],
            0 <= big_j <= s.len(),
        ensures
            Self::count_le_upto(s, num1, den1, big_j) <= Self::count_le_upto(s, num2, den2, big_j),
        decreases big_j,
    {
        if big_j > 0 {
            Self::lemma_count_le_upto_cross_monotone(s, num1, den1, num2, den2, big_j - 1);
            Self::lemma_count_le_col_cross_monotone(s, big_j - 1, num1, den1, num2, den2);
        }
    }

    proof fn lemma_count_le_cross_monotone(s: Seq<i32>, num1: int, den1: int, num2: int, den2: int)
        requires
            num1 * den2 <= num2 * den1,
            den1 > 0,
            den2 > 0,
            forall|a: int| 0 <= a < s.len() ==> 1 <= #[trigger] s[a],
        ensures
            Self::count_le(s, num1, den1) <= Self::count_le(s, num2, den2),
    {
        Self::lemma_count_le_upto_cross_monotone(s, num1, den1, num2, den2, s.len() as int);
    }

    proof fn lemma_count_le_col_vs_fractions_less(s: Seq<i32>, b: int, num: int, den: int, i0: int, j0: int)
        requires
            den > 0,
            forall|a: int| 0 <= a < s.len() ==> 1 <= #[trigger] s[a],
            0 <= b < s.len(),
            0 <= i0 < j0 < s.len(),
            forall|a: int| 0 <= a < b ==>
                #[trigger] Self::frac_le(s, a, b, num, den) ==> Self::fraction_less(s, a, b, i0, j0),
        ensures
            Self::count_le_col(s, b, num, den) <= Self::count_col_less(s, b, i0, j0),
    {
        Self::lemma_count_le_col_vs_fractions_less_from(s, 0, b, num, den, i0, j0);
    }

    proof fn lemma_count_le_col_vs_fractions_less_from(s: Seq<i32>, a0: int, b: int, num: int, den: int, i0: int, j0: int)
        requires
            den > 0,
            forall|a: int| 0 <= a < s.len() ==> 1 <= #[trigger] s[a],
            0 <= a0 <= b < s.len(),
            0 <= i0 < j0 < s.len(),
            forall|a: int| a0 <= a < b ==>
                #[trigger] Self::frac_le(s, a, b, num, den) ==> Self::fraction_less(s, a, b, i0, j0),
        ensures
            Self::count_le_col_from(s, a0, b, num, den) <= Self::count_col_less_from(s, a0, b, i0, j0),
        decreases b - a0,
    {
        if a0 < b {
            Self::lemma_count_le_col_vs_fractions_less_from(s, a0 + 1, b, num, den, i0, j0);
        }
    }

    proof fn lemma_count_le_upto_vs_fractions_less(s: Seq<i32>, num: int, den: int, i0: int, j0: int, big_j: int)
        requires
            den > 0,
            forall|a: int| 0 <= a < s.len() ==> 1 <= #[trigger] s[a],
            0 <= i0 < j0 < s.len(),
            0 <= big_j <= s.len(),
            forall|a: int, b: int| 0 <= a < b < s.len() ==>
                #[trigger] Self::frac_le(s, a, b, num, den) ==> Self::fraction_less(s, a, b, i0, j0),
        ensures
            Self::count_le_upto(s, num, den, big_j) <= Self::count_cols_upto(s, i0, j0, big_j),
        decreases big_j,
    {
        if big_j > 0 {
            Self::lemma_count_le_upto_vs_fractions_less(s, num, den, i0, j0, big_j - 1);
            Self::lemma_count_le_col_vs_fractions_less(s, big_j - 1, num, den, i0, j0);
        }
    }

    proof fn lemma_count_le_lower(s: Seq<i32>, lo: int, den: int, i0: int, j0: int)
        requires
            s[0] == 1,
            forall|i: int| 0 <= i < s.len() ==> 1 <= #[trigger] s[i] <= 30_000,
            forall|i: int| 1 <= i < s.len() ==> #[trigger] Self::is_prime(s[i] as int),
            forall|i: int, j2: int| 0 <= i < j2 < s.len() ==> s[i] < s[j2],
            1 <= j0 < s.len(),
            0 <= i0 < j0,
            den > 0,
            Self::count_le(s, lo, den) < Self::count_fractions_less(s, i0, j0) + 1,
        ensures
            lo * (s[j0] as int) < (s[i0] as int) * den,
    {
        Self::lemma_count_le_exact(s, i0, j0);
        if (s[i0] as int) * den <= lo * (s[j0] as int) {
            Self::lemma_count_le_cross_monotone(s, s[i0] as int, s[j0] as int, lo, den);
            assert(Self::count_le(s, s[i0] as int, s[j0] as int) <= Self::count_le(s, lo, den));
            assert(false);
        }
    }

    proof fn lemma_count_le_upper(s: Seq<i32>, hi: int, den: int, i0: int, j0: int)
        requires
            s[0] == 1,
            forall|i: int| 0 <= i < s.len() ==> 1 <= #[trigger] s[i] <= 30_000,
            forall|i: int| 1 <= i < s.len() ==> #[trigger] Self::is_prime(s[i] as int),
            forall|i: int, j2: int| 0 <= i < j2 < s.len() ==> s[i] < s[j2],
            1 <= j0 < s.len(),
            0 <= i0 < j0,
            den > 0,
            Self::count_le(s, hi, den) >= Self::count_fractions_less(s, i0, j0) + 1,
        ensures
            (s[i0] as int) * den <= hi * (s[j0] as int),
    {
        if hi * (s[j0] as int) < (s[i0] as int) * den {
            assert forall|a: int, b: int| 0 <= a < b < s.len() implies
                #[trigger] Self::frac_le(s, a, b, hi, den) ==> Self::fraction_less(s, a, b, i0, j0) by {
                if Self::frac_le(s, a, b, hi, den) {
                    assert((s[a] as int) * den <= hi * (s[b] as int));
                    assert(((s[a] as int) * den) * (s[j0] as int)
                        <= (hi * (s[b] as int)) * (s[j0] as int)) by (nonlinear_arith)
                        requires
                            (s[a] as int) * den <= hi * (s[b] as int),
                            s[j0] as int >= 0,
                    {
                    }
                    assert((hi * (s[j0] as int)) * (s[b] as int)
                        < ((s[i0] as int) * den) * (s[b] as int)) by (nonlinear_arith)
                        requires
                            hi * (s[j0] as int) < (s[i0] as int) * den,
                            s[b] as int >= 1,
                    {
                    }
                    assert(((s[a] as int) * den) * (s[j0] as int)
                        < ((s[i0] as int) * den) * (s[b] as int)) by (nonlinear_arith)
                        requires
                            ((s[a] as int) * den) * (s[j0] as int) <= (hi * (s[b] as int)) * (s[j0] as int),
                            (hi * (s[j0] as int)) * (s[b] as int) < ((s[i0] as int) * den) * (s[b] as int),
                    {
                    }
                    assert((s[a] as int) * (s[j0] as int) < (s[i0] as int) * (s[b] as int)) by (nonlinear_arith)
                        requires
                            ((s[a] as int) * den) * (s[j0] as int) < ((s[i0] as int) * den) * (s[b] as int),
                            den > 0,
                    {
                    }
                }
            }
            Self::lemma_count_le_upto_vs_fractions_less(s, hi, den, i0, j0, s.len() as int);
            Self::lemma_count_fractions_less_col(s, i0, j0);
            assert(Self::count_le(s, hi, den) <= Self::count_fractions_less(s, i0, j0));
            assert(false);
        }
    }


    proof fn lemma_uniqueness_pointwise(s: Seq<i32>, lo: int, hi: int, den: int, i0: int, j0: int, a: int, b: int)
        requires
            s[0] == 1,
            forall|i: int| 0 <= i < s.len() ==> 1 <= #[trigger] s[i] <= 30_000,
            forall|i: int| 1 <= i < s.len() ==> #[trigger] Self::is_prime(s[i] as int),
            forall|i: int, j2: int| 0 <= i < j2 < s.len() ==> s[i] < s[j2],
            1 <= j0 < s.len(),
            0 <= i0 < j0,
            0 <= a < b < s.len(),
            den >= 1_100_000_000,
            hi == lo + 1,
            lo * (s[j0] as int) < (s[i0] as int) * den,
            (a, b) != (i0, j0),
            Self::frac_le(s, a, b, hi, den),
        ensures
            Self::fraction_less(s, a, b, i0, j0),
    {
        if !Self::fraction_less(s, a, b, i0, j0) {
            assert((s[a] as int) * (s[j0] as int) >= (s[i0] as int) * (s[b] as int));
            assert((s[a] as int) * (s[j0] as int) != (s[i0] as int) * (s[b] as int)) by {
                if b == j0 {
                    if a < i0 {
                        assert(s[a] < s[i0]);
                        assert((s[a] as int) * (s[j0] as int) < (s[i0] as int) * (s[b] as int)) by (nonlinear_arith)
                            requires
                                (s[a] as int) < (s[i0] as int),
                                (s[j0] as int) >= 1,
                                b == j0,
                        {
                        }
                        assert(false);
                    } else {
                        assert(a != i0);
                        assert(a > i0);
                        assert(s[i0] < s[a]);
                        assert((s[a] as int) * (s[j0] as int) > (s[i0] as int) * (s[b] as int)) by (nonlinear_arith)
                            requires
                                (s[i0] as int) < (s[a] as int),
                                (s[j0] as int) >= 1,
                                b == j0,
                        {
                        }
                    }
                } else {
                    assert(1 <= b < s.len());
                    assert(0 <= a < b);
                    assert(1 <= j0 < s.len());
                    assert(0 <= i0 < j0);
                    Self::lemma_fractions_distinct(s, b, a, j0, i0);
                }
            };
            assert((s[a] as int) * (s[j0] as int) > (s[i0] as int) * (s[b] as int));
            // Step 1: sa*sj0 >= si0*sb + 1
            assert((s[a] as int) * (s[j0] as int) >= (s[i0] as int) * (s[b] as int) + 1) by (nonlinear_arith)
                requires
                    (s[a] as int) * (s[j0] as int) > (s[i0] as int) * (s[b] as int),
            {
            }
            // Step 2: sa*sj0*den >= (si0*sb+1)*den == si0*sb*den + den
            assert(((s[a] as int) * (s[j0] as int)) * den
                >= (s[i0] as int) * (s[b] as int) * den + den) by (nonlinear_arith)
                requires
                    (s[a] as int) * (s[j0] as int) >= (s[i0] as int) * (s[b] as int) + 1,
                    den >= 1,
            {
            }
            // Step 3: sa*den <= hi*sb (given frac_le), times sj0
            assert((s[a] as int) * den <= hi * (s[b] as int));
            assert(((s[a] as int) * den) * (s[j0] as int) <= (hi * (s[b] as int)) * (s[j0] as int)) by (nonlinear_arith)
                requires
                    (s[a] as int) * den <= hi * (s[b] as int),
                    (s[j0] as int) >= 0,
            {
            }
            // Step 4: combine 2,3: hi*sb*sj0 >= si0*sb*den + den
            assert(hi * (s[b] as int) * (s[j0] as int) >= (s[i0] as int) * (s[b] as int) * den + den)
                by (nonlinear_arith)
                requires
                    ((s[a] as int) * (s[j0] as int)) * den >= (s[i0] as int) * (s[b] as int) * den + den,
                    ((s[a] as int) * den) * (s[j0] as int) <= (hi * (s[b] as int)) * (s[j0] as int),
            {
            }
            // Step 5: expand hi = lo + 1
            assert(hi * (s[b] as int) * (s[j0] as int)
                == lo * (s[b] as int) * (s[j0] as int) + (s[b] as int) * (s[j0] as int)) by (nonlinear_arith)
                requires
                    hi == lo + 1,
            {
            }
            // Step 6: lo*sj0 < si0*den, times sb
            assert(lo * (s[j0] as int) * (s[b] as int)
                <= (s[i0] as int) * den * (s[b] as int) - (s[b] as int)) by (nonlinear_arith)
                requires
                    lo * (s[j0] as int) < (s[i0] as int) * den,
                    (s[b] as int) >= 1,
            {
            }
            // Step 7: combine 4,5,6 to derive den <= sb*(sj0-1)
            assert(den <= (s[b] as int) * ((s[j0] as int) - 1)) by (nonlinear_arith)
                requires
                    hi * (s[b] as int) * (s[j0] as int) >= (s[i0] as int) * (s[b] as int) * den + den,
                    hi * (s[b] as int) * (s[j0] as int)
                        == lo * (s[b] as int) * (s[j0] as int) + (s[b] as int) * (s[j0] as int),
                    lo * (s[j0] as int) * (s[b] as int) <= (s[i0] as int) * den * (s[b] as int) - (s[b] as int),
            {
            }
            assert((s[b] as int) <= 30_000);
            assert((s[j0] as int) - 1 <= 29_999);
            assert(den <= 30_000 * 29_999) by (nonlinear_arith)
                requires
                    den <= (s[b] as int) * ((s[j0] as int) - 1),
                    (s[b] as int) <= 30_000,
                    (s[j0] as int) - 1 <= 29_999,
                    (s[b] as int) >= 1,
                    (s[j0] as int) - 1 >= 0,
            {
            }
            assert(false);
        }
    }

    proof fn lemma_frac_le_scale_minus_one_at(s: Seq<i32>, scale: int, a: int, b: int)
        requires
            forall|i: int| 0 <= i < s.len() ==> 1 <= #[trigger] s[i] <= 30_000,
            forall|i: int, j2: int| 0 <= i < j2 < s.len() ==> s[i] < s[j2],
            0 <= a < b < s.len(),
            scale >= 30_000,
        ensures
            Self::frac_le(s, a, b, scale - 1, scale) == Self::frac_le(s, a, b, scale, scale),
    {
        assert(s[a] < s[b]);
        assert((s[a] as int) * scale <= scale * (s[b] as int)) by (nonlinear_arith)
            requires
                (s[a] as int) <= (s[b] as int),
                scale >= 0,
        {
        }
        assert((s[a] as int) * scale <= (scale - 1) * (s[b] as int)) by (nonlinear_arith)
            requires
                (s[a] as int) < (s[b] as int),
                (s[b] as int) <= 30_000,
                scale >= 30_000,
        {
        }
    }

    proof fn lemma_count_le_col_scale_minus_one_from(s: Seq<i32>, a0: int, j: int, scale: int)
        requires
            forall|i: int| 0 <= i < s.len() ==> 1 <= #[trigger] s[i] <= 30_000,
            forall|i: int, j2: int| 0 <= i < j2 < s.len() ==> s[i] < s[j2],
            0 <= a0 <= j < s.len(),
            scale >= 30_000,
        ensures
            Self::count_le_col_from(s, a0, j, scale - 1, scale) == Self::count_le_col_from(s, a0, j, scale, scale),
        decreases j - a0,
    {
        if a0 < j {
            Self::lemma_count_le_col_scale_minus_one_from(s, a0 + 1, j, scale);
            Self::lemma_frac_le_scale_minus_one_at(s, scale, a0, j);
        }
    }

    proof fn lemma_count_le_upto_scale_minus_one(s: Seq<i32>, scale: int, big_j: int)
        requires
            forall|i: int| 0 <= i < s.len() ==> 1 <= #[trigger] s[i] <= 30_000,
            forall|i: int, j2: int| 0 <= i < j2 < s.len() ==> s[i] < s[j2],
            0 <= big_j <= s.len(),
            scale >= 30_000,
        ensures
            Self::count_le_upto(s, scale - 1, scale, big_j) == Self::count_le_upto(s, scale, scale, big_j),
        decreases big_j,
    {
        if big_j > 0 {
            Self::lemma_count_le_upto_scale_minus_one(s, scale, big_j - 1);
            Self::lemma_count_le_col_scale_minus_one_from(s, 0, big_j - 1, scale);
        }
    }

    proof fn lemma_count_le_scale_minus_one(s: Seq<i32>, scale: int)
        requires
            forall|i: int| 0 <= i < s.len() ==> 1 <= #[trigger] s[i] <= 30_000,
            forall|i: int, j2: int| 0 <= i < j2 < s.len() ==> s[i] < s[j2],
            scale >= 30_000,
        ensures
            Self::count_le(s, scale - 1, scale) == Self::count_le(s, scale, scale),
    {
        Self::lemma_count_le_upto_scale_minus_one(s, scale, s.len() as int);
    }


    proof fn lemma_count_le_col_all_false(s: Seq<i32>, j: int, num: int, den: int)
        requires
            0 <= j < s.len(),
            forall|a: int| 0 <= a < j ==> !(#[trigger] Self::frac_le(s, a, j, num, den)),
        ensures
            Self::count_le_col(s, j, num, den) == 0nat,
    {
        Self::lemma_count_le_col_all_false_from(s, 0, j, num, den);
    }

    proof fn lemma_count_le_col_all_false_from(s: Seq<i32>, a0: int, j: int, num: int, den: int)
        requires
            0 <= a0 <= j < s.len(),
            forall|a: int| a0 <= a < j ==> !(#[trigger] Self::frac_le(s, a, j, num, den)),
        ensures
            Self::count_le_col_from(s, a0, j, num, den) == 0nat,
        decreases j - a0,
    {
        if a0 < j {
            Self::lemma_count_le_col_all_false_from(s, a0 + 1, j, num, den);
        }
    }

    proof fn lemma_count_le_all_false_upto(s: Seq<i32>, den: int, big_j: int)
        requires
            0 <= big_j <= s.len(),
            forall|a: int, b: int| 0 <= a < b < s.len() ==> !(#[trigger] Self::frac_le(s, a, b, 0, den)),
        ensures
            Self::count_le_upto(s, 0, den, big_j) == 0nat,
        decreases big_j,
    {
        if big_j > 0 {
            Self::lemma_count_le_all_false_upto(s, den, big_j - 1);
            Self::lemma_count_le_col_all_false(s, big_j - 1, 0, den);
        }
    }

    proof fn lemma_not_less_trans(s: Seq<i32>, oi: int, oj: int, a: int, b: int, ni: int, nj: int)
        requires
            0 <= oi < s.len(),
            0 <= oj < s.len(),
            1 <= s[oj],
            0 <= a < s.len(),
            0 <= b < s.len(),
            1 <= s[b],
            0 <= ni < s.len(),
            0 <= nj < s.len(),
            1 <= s[nj],
            !Self::fraction_less(s, oi, oj, a, b),
            !Self::fraction_less(s, ni, nj, oi, oj),
        ensures
            !Self::fraction_less(s, ni, nj, a, b),
    {
        assert((s[oi] as int) * (s[b] as int) >= (s[a] as int) * (s[oj] as int));
        assert((s[ni] as int) * (s[oj] as int) >= (s[oi] as int) * (s[nj] as int));
        assert(((s[oi] as int) * (s[b] as int)) * (s[nj] as int)
            >= ((s[a] as int) * (s[oj] as int)) * (s[nj] as int)) by (nonlinear_arith)
            requires
                (s[oi] as int) * (s[b] as int) >= (s[a] as int) * (s[oj] as int),
                (s[nj] as int) >= 1,
        {
        }
        assert(((s[ni] as int) * (s[oj] as int)) * (s[b] as int)
            >= ((s[oi] as int) * (s[nj] as int)) * (s[b] as int)) by (nonlinear_arith)
            requires
                (s[ni] as int) * (s[oj] as int) >= (s[oi] as int) * (s[nj] as int),
                (s[b] as int) >= 1,
        {
        }
        assert(((s[ni] as int) * (s[b] as int)) * (s[oj] as int)
            >= ((s[a] as int) * (s[nj] as int)) * (s[oj] as int)) by (nonlinear_arith)
            requires
                ((s[oi] as int) * (s[b] as int)) * (s[nj] as int) >= ((s[a] as int) * (s[oj] as int)) * (s[nj] as int),
                ((s[ni] as int) * (s[oj] as int)) * (s[b] as int) >= ((s[oi] as int) * (s[nj] as int)) * (s[b] as int),
        {
        }
        assert((s[ni] as int) * (s[b] as int) >= (s[a] as int) * (s[nj] as int)) by (nonlinear_arith)
            requires
                ((s[ni] as int) * (s[b] as int)) * (s[oj] as int) >= ((s[a] as int) * (s[nj] as int)) * (s[oj] as int),
                (s[oj] as int) > 0,
        {
        }
    }

    proof fn lemma_count_le_col_bound_from(s: Seq<i32>, a0: int, j: int, num: int, den: int)
        requires
            0 <= a0 <= j,
        ensures
            Self::count_le_col_from(s, a0, j, num, den) <= (j - a0) as nat,
        decreases j - a0,
    {
        if a0 < j {
            Self::lemma_count_le_col_bound_from(s, a0 + 1, j, num, den);
        }
    }

    proof fn lemma_count_le_col_bound(s: Seq<i32>, j: int, num: int, den: int)
        requires
            0 <= j,
        ensures
            Self::count_le_col(s, j, num, den) <= j as nat,
    {
        Self::lemma_count_le_col_bound_from(s, 0, j, num, den);
    }

    proof fn lemma_count_le_upto_bound(s: Seq<i32>, num: int, den: int, big_j: int)
        requires
            0 <= big_j,
        ensures
            Self::count_le_upto(s, num, den, big_j) <= (big_j * (big_j - 1) / 2) as nat,
        decreases big_j,
    {
        if big_j > 0 {
            Self::lemma_count_le_upto_bound(s, num, den, big_j - 1);
            Self::lemma_count_le_col_bound(s, big_j - 1, num, den);
            let l = big_j;
            assert((l - 1) + ((l - 1) * (l - 2) / 2) == l * (l - 1) / 2) by (nonlinear_arith);
        }
    }

    proof fn lemma_count_le_col_all_false_gen(s: Seq<i32>, j: int, num: int, den: int)
        requires
            0 <= j < s.len(),
            forall|a: int, b: int| 0 <= a < b < s.len() ==> !(#[trigger] Self::frac_le(s, a, b, num, den)),
        ensures
            Self::count_le_col(s, j, num, den) == 0nat,
    {
        Self::lemma_count_le_col_all_false_from_gen(s, 0, j, num, den);
    }

    proof fn lemma_count_le_col_all_false_from_gen(s: Seq<i32>, a0: int, j: int, num: int, den: int)
        requires
            0 <= a0 <= j < s.len(),
            forall|a: int, b: int| 0 <= a < b < s.len() ==> !(#[trigger] Self::frac_le(s, a, b, num, den)),
        ensures
            Self::count_le_col_from(s, a0, j, num, den) == 0nat,
        decreases j - a0,
    {
        if a0 < j {
            Self::lemma_count_le_col_all_false_from_gen(s, a0 + 1, j, num, den);
        }
    }

    proof fn lemma_count_le_all_false_upto_gen(s: Seq<i32>, num: int, den: int, big_j: int)
        requires
            0 <= big_j <= s.len(),
            forall|a: int, b: int| 0 <= a < b < s.len() ==> !(#[trigger] Self::frac_le(s, a, b, num, den)),
        ensures
            Self::count_le_upto(s, num, den, big_j) == 0nat,
        decreases big_j,
    {
        if big_j > 0 {
            Self::lemma_count_le_all_false_upto_gen(s, num, den, big_j - 1);
            Self::lemma_count_le_col_all_false_gen(s, big_j - 1, num, den);
        }
    }
    #[verifier::loop_isolation(false)]
    pub fn kth_smallest_prime_fraction(arr: Vec<i32>, k: i32) -> (result: Vec<i32>)
        requires
            2 <= arr.len() <= 1000,
            forall|i: int| 0 <= i < arr.len() ==> 1 <= #[trigger] arr[i] <= 30_000,
            arr[0] == 1,
            forall|i: int| 1 <= i < arr.len() ==> #[trigger] Self::is_prime(arr[i] as int),
            forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] < arr[j],
            1 <= k <= (arr.len() * (arr.len() - 1) / 2) as int,
            exists|i: int, j: int|
                0 <= i < j < arr.len()
                && #[trigger] Self::count_fractions_less(arr@, i, j) == (k - 1) as nat,
        ensures
            result.len() == 2,
            exists|i: int, j: int|
                0 <= i < j < arr.len()
                && #[trigger] result@[0] == arr@[i]
                && result@[1] == arr@[j]
                && Self::count_fractions_less(arr@, i, j) == (k - 1) as nat,
    {
        let n = arr.len();
        let ghost pair0: (int, int) = choose|i0: int, j0: int|
            0 <= i0 < j0 < arr@.len()
                && #[trigger] Self::count_fractions_less(arr@, i0, j0) == (k - 1) as nat;
        let ghost i0: int = pair0.0;
        let ghost j0: int = pair0.1;

        let scale: i64 = 1i64 << 32;
        let mut lo: i64 = 0;
        let mut hi: i64 = scale;
        let mut ans_i: usize = 0;
        let mut ans_j: usize = 1;
        let ghost mut has_result: bool = false;

        proof {
            assert(scale as int == 4_294_967_296) by (bit_vector)
                requires scale == 1i64 << 32;
            assert(0 <= i0 < j0 < n as int);
            assert(Self::count_fractions_less(arr@, i0, j0) == (k - 1) as nat);
            Self::lemma_count_le_exact(arr@, i0, j0);
            assert(Self::count_le(arr@, arr@[i0] as int, arr@[j0] as int) == k as int);
            assert((arr@[i0] as int) * scale as int <= (scale as int) * (arr@[j0] as int)) by (nonlinear_arith)
                requires
                    arr@[i0] as int <= arr@[j0] as int,
                    scale as int >= 0,
            {
            }
            Self::lemma_count_le_cross_monotone(arr@, arr@[i0] as int, arr@[j0] as int, scale as int, scale as int);
            assert(Self::count_le(arr@, scale as int, scale as int) >= k as int);
            assert forall|a: int, b: int| 0 <= a < b < n as int implies
                !(#[trigger] Self::frac_le(arr@, a, b, 0, scale as int)) by {
                assert(1 <= arr@[a]);
                assert(scale as int >= 1);
                assert((arr@[a] as int) * (scale as int) >= scale as int) by (nonlinear_arith)
                    requires
                        arr@[a] as int >= 1,
                        scale as int >= 0,
                {
                }
            }
            Self::lemma_count_le_all_false_upto(arr@, scale as int, n as int);
            assert(Self::count_le(arr@, 0, scale as int) == 0);
            assert(scale >> 0u32 == scale) by (bit_vector);
        }

        let mut iter: u32 = 0;
        while iter < 32
            invariant
                iter <= 32,
                n == arr@.len(),
                2 <= n <= 1000,
                forall|i: int| 0 <= i < n as int ==> 1 <= #[trigger] arr@[i] <= 30_000,
                arr@[0] == 1,
                forall|i: int| 1 <= i < n as int ==> #[trigger] Self::is_prime(arr@[i] as int),
                forall|i: int, j: int| 0 <= i < j < n as int ==> arr@[i] < arr@[j],
                0 <= i0 < j0 < n as int,
                Self::count_fractions_less(arr@, i0, j0) == (k - 1) as nat,
                scale == 1i64 << 32,
                0 <= lo < hi <= scale,
                hi - lo == scale >> iter,
                Self::count_le(arr@, lo as int, scale as int) < k as int,
                Self::count_le(arr@, hi as int, scale as int) >= k as int,
                1 <= ans_j < n,
                ans_i < ans_j,
                !has_result ==> hi == scale,
                has_result ==> Self::frac_le(arr@, ans_i as int, ans_j as int, hi as int, scale as int),
                has_result ==> forall|a: int, b: int| 0 <= a < b < n as int
                    ==> (#[trigger] Self::frac_le(arr@, a, b, hi as int, scale as int)
                        ==> !Self::fraction_less(arr@, ans_i as int, ans_j as int, a, b)),
            decreases 32 - iter,
        {
            let mid: i64 = lo + (hi - lo) / 2;
            proof {
                assert(0 <= lo);
                assert(mid <= hi);
                assert(hi <= scale);
            }
            let mut count: i32 = 0;
            let mut best_i: usize = 0;
            let mut best_j: usize = 1;
            let mut found: bool = false;
            let mut i: usize = 0;
            let mut j: usize = 1;
            proof {
                assert(Self::count_le_col(arr@, 0, mid as int, scale as int) == 0nat);
                assert(Self::count_le_upto(arr@, mid as int, scale as int, 0) == 0nat);
                assert(Self::count_le_upto(arr@, mid as int, scale as int, 1)
                    == Self::count_le_col(arr@, 0, mid as int, scale as int)
                        + Self::count_le_upto(arr@, mid as int, scale as int, 0));
            }
            while j < n
                invariant
                    n == arr@.len(),
                    2 <= n <= 1000,
                    forall|t: int| 0 <= t < n as int ==> 1 <= #[trigger] arr@[t] <= 30_000,
                    forall|t: int, u: int| 0 <= t < u < n as int ==> arr@[t] < arr@[u],
                    1 <= j <= n,
                    0 <= mid <= scale,
                    scale == 4_294_967_296,
                    count as int == Self::count_le_upto(arr@, mid as int, scale as int, j as int),
                    0 <= count as int <= 500_000,
                    found ==> Self::frac_le(arr@, best_i as int, best_j as int, mid as int, scale as int),
                    found ==> forall|a: int, b: int| 0 <= a < b < j as int
                        ==> (#[trigger] Self::frac_le(arr@, a, b, mid as int, scale as int)
                            ==> !Self::fraction_less(arr@, best_i as int, best_j as int, a, b)),
                    !found ==> forall|a: int, b: int| 0 <= a < b < j as int
                        ==> !#[trigger] Self::frac_le(arr@, a, b, mid as int, scale as int),
                    1 <= best_j < n,
                    best_i < best_j,
                decreases n - j,
            {
                i = 0;
                proof {
                    assert(count as int == Self::count_le_upto(arr@, mid as int, scale as int, j as int));
                    assert(1 <= arr@[j as int] <= 30_000);
                    assert(mid * (arr@[j as int] as i64) <= scale * 30_000) by (nonlinear_arith)
                        requires
                            0 <= mid <= scale,
                    scale == 4_294_967_296,
                            arr@[j as int] as i64 <= 30_000,
                    {
                    }
                    assert(scale * 30_000 <= 9_000_000_000_000_000_000i64) by (nonlinear_arith)
                        requires
                            scale == 4_294_967_296,
                    {
                    }
                }
                while i < j && (arr[i] as i64) * scale <= mid * (arr[j] as i64)
                    invariant
                        n == arr@.len(),
                        2 <= n <= 1000,
                        forall|t: int| 0 <= t < n as int ==> 1 <= #[trigger] arr@[t] <= 30_000,
                        forall|t: int, u: int| 0 <= t < u < n as int ==> arr@[t] < arr@[u],
                        1 <= j < n,
                        0 <= i <= j,
                        0 <= mid <= scale,
                    scale == 4_294_967_296,
                        forall|a: int| 0 <= a < i as int ==>
                            #[trigger] Self::frac_le(arr@, a, j as int, mid as int, scale as int),
                        found ==> Self::frac_le(arr@, best_i as int, best_j as int, mid as int, scale as int),
                        found ==> forall|a: int, b: int|
                            0 <= a < b < j as int || (b as int == j as int && 0 <= a < i as int)
                            ==> (#[trigger] Self::frac_le(arr@, a, b, mid as int, scale as int)
                                ==> !Self::fraction_less(arr@, best_i as int, best_j as int, a, b)),
                        !found ==> forall|a: int, b: int|
                            (0 <= a < b < j as int || (b as int == j as int && 0 <= a < i as int))
                            ==> !#[trigger] Self::frac_le(arr@, a, b, mid as int, scale as int),
                        1 <= best_j < n,
                        best_i < best_j,
                    decreases j - i,
                {
                    proof {
                        assert(0 <= i as int && (i as int) < (j as int));
                        assert(1 <= arr@[i as int] <= 30_000);
                        assert(1 <= arr@[j as int] <= 30_000);
                        assert(1 <= arr@[best_i as int] <= 30_000);
                        assert(1 <= arr@[best_j as int] <= 30_000);
                        assert((arr@[i as int] as i64) * (arr@[best_j as int] as i64) <= 900_000_000)
                            by (nonlinear_arith)
                            requires
                                1 <= arr@[i as int] as i64 <= 30_000,
                                1 <= arr@[best_j as int] as i64 <= 30_000;
                        assert((arr@[best_i as int] as i64) * (arr@[j as int] as i64) <= 900_000_000)
                            by (nonlinear_arith)
                            requires
                                1 <= arr@[best_i as int] as i64 <= 30_000,
                                1 <= arr@[j as int] as i64 <= 30_000;
                    }
                    let take = if !found {
                        true
                    } else {
                        (arr[i] as i64) * (arr[best_j] as i64) >= (arr[best_i] as i64) * (arr[j] as i64)
                    };
                    if take {
                        let ghost old_best_i: int = best_i as int;
                        let ghost old_best_j: int = best_j as int;
                        let ghost old_found: bool = found;
                        proof {
                            if old_found {
                                assert(!Self::fraction_less(arr@, i as int, j as int, old_best_i, old_best_j));
                                assert forall|a: int, b: int|
                                    0 <= a < b < j as int || (b as int == j as int && 0 <= a < i as int)
                                    implies (#[trigger] Self::frac_le(arr@, a, b, mid as int, scale as int)
                                        ==> !Self::fraction_less(arr@, i as int, j as int, a, b)) by {
                                    if Self::frac_le(arr@, a, b, mid as int, scale as int) {
                                        assert(!Self::fraction_less(arr@, old_best_i, old_best_j, a, b));
                                        assert(1 <= arr@[a] <= 30_000);
                                        assert(1 <= arr@[b] <= 30_000);
                                        assert(1 <= arr@[old_best_i] <= 30_000);
                                        assert(1 <= arr@[old_best_j] <= 30_000);
                                        assert(1 <= arr@[i as int] <= 30_000);
                                        assert(1 <= arr@[j as int] <= 30_000);
                                        Self::lemma_not_less_trans(
                                            arr@,
                                            old_best_i, old_best_j,
                                            a, b,
                                            i as int, j as int,
                                        );
                                    }
                                }
                            } else {
                                assert forall|a: int, b: int|
                                    0 <= a < b < j as int || (b as int == j as int && 0 <= a < i as int)
                                    implies (#[trigger] Self::frac_le(arr@, a, b, mid as int, scale as int)
                                        ==> !Self::fraction_less(arr@, i as int, j as int, a, b)) by {
                                }
                            }
                        }
                        best_i = i;
                        best_j = j;
                        found = true;
                    }
                    i += 1;
                }
                let ghost found_before_incr: bool = found;
                proof {
                    assert(forall|a: int| 0 <= a < i as int ==>
                        #[trigger] Self::frac_le(arr@, a, j as int, mid as int, scale as int));
                    if i < j {
                        assert(!((arr@[i as int] as i64) * scale <= mid * (arr@[j as int] as i64)));
                        assert(!Self::frac_le(arr@, i as int, j as int, mid as int, scale as int));
                        assert forall|a: int| i as int <= a < j as int implies
                            !(#[trigger] Self::frac_le(arr@, a, j as int, mid as int, scale as int)) by {
                            if a > i as int {
                                assert(arr@[i as int] < arr@[a]);
                                assert((arr@[a] as int) * scale as int
                                    >= (arr@[i as int] as int) * scale as int) by (nonlinear_arith)
                                    requires
                                        arr@[i as int] as int <= arr@[a] as int,
                                        scale as int >= 0,
                                {
                                }
                            }
                        }
                    }
                    Self::lemma_count_le_col_threshold(arr@, j as int, mid as int, scale as int, i as int);
                    assert(Self::count_le_col(arr@, j as int, mid as int, scale as int) == i as nat);
                    if found_before_incr {
                        assert forall|a: int, b: int| 0 <= a < b < j as int + 1 implies
                            (#[trigger] Self::frac_le(arr@, a, b, mid as int, scale as int)
                                ==> !Self::fraction_less(arr@, best_i as int, best_j as int, a, b)) by {
                            if Self::frac_le(arr@, a, b, mid as int, scale as int) {
                                if b < j as int || (b == j as int && a < i as int) {
                                    assert(!Self::fraction_less(arr@, best_i as int, best_j as int, a, b));
                                } else {
                                    assert(b == j as int && a >= i as int);
                                    assert(false);
                                }
                            }
                        }
                    } else {
                        assert forall|a: int, b: int| 0 <= a < b < j as int + 1 implies
                            !(#[trigger] Self::frac_le(arr@, a, b, mid as int, scale as int)) by {
                            if b < j as int {
                            } else {
                                assert(b == j as int);
                                if a < i as int {
                                } else {
                                }
                            }
                        }
                    }
                }
                proof {
                    Self::lemma_count_le_upto_bound(arr@, mid as int, scale as int, j as int + 1);
                    assert(Self::count_le_upto(arr@, mid as int, scale as int, j as int + 1)
                        == Self::count_le_col(arr@, j as int, mid as int, scale as int)
                            + Self::count_le_upto(arr@, mid as int, scale as int, j as int));
                    assert(count as int + (i as int)
                        <= (j as int + 1) * (j as int) / 2);
                    assert(1 <= j as int);
                    assert((j as int) < (n as int));
                    assert((n as int) <= 1000);
                    assert(j as int <= 999);
                    assert((j as int + 1) * (j as int) <= 1_000_000) by (nonlinear_arith)
                        requires 1 <= j as int <= 999;
                    assert((j as int + 1) * (j as int) / 2 <= 500_000) by (nonlinear_arith)
                        requires (j as int + 1) * (j as int) <= 1_000_000;
                }
                count = count + (i as i32);
                proof {
                    assert(count as int == Self::count_le_upto(arr@, mid as int, scale as int, j as int)
                        + Self::count_le_col(arr@, j as int, mid as int, scale as int));
                }
                j += 1;
            }

            proof {
                assert(count as int == Self::count_le_upto(arr@, mid as int, scale as int, n as int));
                assert(Self::count_le(arr@, mid as int, scale as int)
                    == Self::count_le_upto(arr@, mid as int, scale as int, n as int));
            }

            let width_before: i64 = hi - lo;
            let half: i64 = width_before / 2;
            let rest: i64 = width_before - half;
            proof {
                assert(width_before == scale >> iter);
                assert((scale >> iter) >> 1u32 == scale >> (iter + 1)) by (bit_vector);
                assert(half == width_before >> 1u32) by (bit_vector)
                    requires half == width_before / 2;
                assert(mid as int == lo + half);
                assert(hi - mid == rest as int);
                assert((scale >> iter) % 2 == 0) by (bit_vector)
                    requires iter < 32, scale == 1i64 << 32;
                assert(width_before % 2 == 0);
                assert(rest == width_before >> 1u32) by (bit_vector)
                    requires
                        rest == width_before - half,
                        half == width_before >> 1u32,
                        width_before % 2 == 0;
            }
            if count < k {
                proof {
                    assert(Self::count_le(arr@, mid as int, scale as int) < k as int);
                }
                lo = mid;
            } else {
                proof {
                    assert(Self::count_le(arr@, mid as int, scale as int) >= k as int);
                    if !found {
                        assert(forall|a: int, b: int| 0 <= a < b < n as int
                            ==> !#[trigger] Self::frac_le(arr@, a, b, mid as int, scale as int));
                        Self::lemma_count_le_all_false_upto_gen(arr@, mid as int, scale as int, n as int);
                        assert(Self::count_le_upto(arr@, mid as int, scale as int, n as int) == 0nat);
                        assert(false);
                    }
                    assert(found);
                    assert(Self::frac_le(arr@, best_i as int, best_j as int, mid as int, scale as int));
                    assert forall|a: int, b: int| 0 <= a < b < n as int implies
                        (#[trigger] Self::frac_le(arr@, a, b, mid as int, scale as int)
                            ==> !Self::fraction_less(arr@, best_i as int, best_j as int, a, b)) by {
                    }
                }
                hi = mid;
                ans_i = best_i;
                ans_j = best_j;
                proof {
                    has_result = true;
                }
            }
            iter += 1;
        }

        proof {
            assert(iter == 32u32);
            assert(hi - lo == scale >> iter);
            assert(scale >> iter == scale >> 32u32) by (bit_vector)
                requires iter == 32u32;
            assert(hi - lo == scale >> 32u32);
            assert(scale >> 32u32 == 1) by (bit_vector)
                requires scale == 1i64 << 32;
            assert(hi == lo + 1);

            if !has_result {
                assert(hi as int == scale as int);
                assert(lo as int == scale as int - 1);
                Self::lemma_count_le_scale_minus_one(arr@, scale as int);
                assert(Self::count_le(arr@, lo as int, scale as int)
                    == Self::count_le(arr@, scale as int - 1, scale as int));
                assert(Self::count_le(arr@, lo as int, scale as int) >= k as int);
                assert(false);
            }

            Self::lemma_count_le_lower(arr@, lo as int, scale as int, i0, j0);
            Self::lemma_count_le_upper(arr@, hi as int, scale as int, i0, j0);
            assert(Self::frac_le(arr@, i0, j0, hi as int, scale as int));
            assert(!Self::fraction_less(arr@, ans_i as int, ans_j as int, i0, j0));

            if (ans_i as int, ans_j as int) != (i0, j0) {
                Self::lemma_uniqueness_pointwise(
                    arr@, lo as int, hi as int, scale as int, i0, j0, ans_i as int, ans_j as int,
                );
                assert(Self::fraction_less(arr@, ans_i as int, ans_j as int, i0, j0));
                assert(false);
            }
            assert(ans_i as int == i0);
            assert(ans_j as int == j0);
        }

        let mut result = Vec::new();
        result.push(arr[ans_i]);
        result.push(arr[ans_j]);
        result
    }
}

}
