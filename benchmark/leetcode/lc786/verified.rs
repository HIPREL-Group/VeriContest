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

    proof fn lemma_fraction_less_trans(s: Seq<i32>, a: int, b: int, c: int, d: int, e: int, f: int)
        requires
            0 <= a < s.len(),
            0 <= b < s.len(),
            1 <= s[b],
            0 <= c < s.len(),
            0 <= d < s.len(),
            1 <= s[d],
            0 <= e < s.len(),
            0 <= f < s.len(),
            1 <= s[f],
            Self::fraction_less(s, a, b, c, d),
            !Self::fraction_less(s, e, f, c, d),
        ensures
            Self::fraction_less(s, a, b, e, f),
    {
        assert((s[a] as int) * (s[d] as int) < (s[c] as int) * (s[b] as int));
        assert((s[c] as int) * (s[f] as int) <= (s[e] as int) * (s[d] as int));
        assert(((s[a] as int) * (s[d] as int)) * (s[f] as int)
            < ((s[c] as int) * (s[b] as int)) * (s[f] as int)) by (nonlinear_arith)
            requires
                (s[a] as int) * (s[d] as int) < (s[c] as int) * (s[b] as int),
                (s[f] as int) >= 1,
        {
        }
        assert(((s[c] as int) * (s[f] as int)) * (s[b] as int)
            <= ((s[e] as int) * (s[d] as int)) * (s[b] as int)) by (nonlinear_arith)
            requires
                (s[c] as int) * (s[f] as int) <= (s[e] as int) * (s[d] as int),
                (s[b] as int) >= 1,
        {
        }
        assert(((s[a] as int) * (s[d] as int)) * (s[f] as int)
            < ((s[e] as int) * (s[d] as int)) * (s[b] as int)) by (nonlinear_arith)
            requires
                ((s[a] as int) * (s[d] as int)) * (s[f] as int) < ((s[c] as int) * (s[b] as int)) * (s[f] as int),
                ((s[c] as int) * (s[f] as int)) * (s[b] as int) <= ((s[e] as int) * (s[d] as int)) * (s[b] as int),
        {
        }
        assert((s[a] as int) * (s[f] as int) < (s[e] as int) * (s[b] as int)) by (nonlinear_arith)
            requires
                ((s[a] as int) * (s[d] as int)) * (s[f] as int) < ((s[e] as int) * (s[d] as int)) * (s[b] as int),
                (s[d] as int) >= 1,
        {
        }
    }

    pub open spec fn order_consistent(s: Seq<i32>, ptr: Seq<int>, n: int) -> bool {
        forall|j1: int, a1: int, j2: int, a2: int|
            (1 <= j1 < n && 0 <= a1 < ptr[j1])
                && (1 <= j2 < n && ptr[j2] <= a2 < j2)
                ==> #[trigger] Self::fraction_less(s, a1, j1, a2, j2)
    }

    proof fn lemma_order_consistent_step(s: Seq<i32>, ptr: Seq<int>, n: int, jstar: int)
        requires
            s.len() == n,
            s[0] == 1,
            forall|i: int| 0 <= i < n ==> 1 <= #[trigger] s[i] <= 30_000,
            forall|i: int| 1 <= i < n ==> #[trigger] Self::is_prime(s[i] as int),
            forall|i: int, j: int| 0 <= i < j < n ==> s[i] < s[j],
            ptr.len() == n,
            forall|j: int| 1 <= j < n ==> 0 <= #[trigger] ptr[j] <= j,
            Self::order_consistent(s, ptr, n),
            1 <= jstar < n,
            ptr[jstar] < jstar,
            forall|j: int|
                (1 <= j < n && ptr[j] < j) ==> !#[trigger] Self::fraction_less(s, ptr[j], j, ptr[jstar], jstar),
        ensures
            Self::order_consistent(s, ptr.update(jstar, ptr[jstar] + 1), n),
    {
        let ptr2 = ptr.update(jstar, ptr[jstar] + 1);
        assert forall|j1: int, a1: int, j2: int, a2: int|
            (1 <= j1 < n && 0 <= a1 < ptr2[j1]) && (1 <= j2 < n && ptr2[j2] <= a2 < j2)
            implies #[trigger] Self::fraction_less(s, a1, j1, a2, j2) by {
            if j1 == jstar && a1 == ptr[jstar] {
                if j2 == jstar {
                    assert(s[a1] < s[a2]);
                    assert((s[a1] as int) * (s[j2] as int) < (s[a2] as int) * (s[j1] as int)) by (nonlinear_arith)
                        requires
                            s[a1] < s[a2],
                            j1 == j2,
                            s[j1] as int >= 1,
                    {
                    }
                } else {
                    if ptr[j2] < j2 {
                        assert(!Self::fraction_less(s, ptr[j2], j2, ptr[jstar], jstar));
                        Self::lemma_fractions_distinct(s, j2, ptr[j2], jstar, ptr[jstar]);
                        assert((s[ptr[j2]] as int) * (s[jstar] as int) != (s[ptr[jstar]] as int) * (s[j2] as int));
                        assert((s[ptr[j2]] as int) * (s[jstar] as int) > (s[ptr[jstar]] as int) * (s[j2] as int));
                        assert(s[ptr[j2]] <= s[a2]);
                        assert((s[a2] as int) * (s[jstar] as int) >= (s[ptr[j2]] as int) * (s[jstar] as int)) by (nonlinear_arith)
                            requires
                                s[ptr[j2]] <= s[a2],
                                s[jstar] as int >= 1,
                        {
                        }
                        assert((s[a1] as int) * (s[j2] as int) < (s[a2] as int) * (s[j1] as int)) by (nonlinear_arith)
                            requires
                                (s[a2] as int) * (s[jstar] as int) >= (s[ptr[j2]] as int) * (s[jstar] as int),
                                (s[ptr[j2]] as int) * (s[jstar] as int) > (s[ptr[jstar]] as int) * (s[j2] as int),
                                a1 == ptr[jstar],
                                j1 == jstar,
                        {
                        }
                    } else {
                        assert(false);
                    }
                }
            } else {
                assert(0 <= a1 < ptr[j1]);
                if j2 == jstar {
                    assert(ptr[j2] <= a2 < j2);
                } else {
                    assert(ptr[j2] <= a2 < j2);
                }
                assert(Self::fraction_less(s, a1, j1, a2, j2));
            }
        }
    }

    pub open spec fn sum_ptr(ptr: Seq<int>, lo: int, hi: int) -> int
        decreases hi - lo,
    {
        if hi <= lo { 0 } else { Self::sum_ptr(ptr, lo, hi - 1) + ptr[hi - 1] }
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

    proof fn lemma_final_count(
        s: Seq<i32>,
        n: int,
        ptr_before: Seq<int>,
        ans_i: int,
        ans_j: int,
        k: int,
    )
        requires
            s.len() == n,
            s[0] == 1,
            forall|i: int| 0 <= i < n ==> 1 <= #[trigger] s[i] <= 30_000,
            forall|i: int| 1 <= i < n ==> #[trigger] Self::is_prime(s[i] as int),
            forall|i: int, j: int| 0 <= i < j < n ==> s[i] < s[j],
            ptr_before.len() == n,
            forall|j: int| 1 <= j < n ==> 0 <= #[trigger] ptr_before[j] <= j,
            1 <= ans_j < n,
            ans_i == ptr_before[ans_j],
            ans_i < ans_j,
            Self::order_consistent(s, ptr_before, n),
            Self::order_consistent(s, ptr_before.update(ans_j, ans_i + 1), n),
            Self::sum_ptr(ptr_before.update(ans_j, ans_i + 1), 1, n) == k,
        ensures
            Self::count_fractions_less(s, ans_i, ans_j) == (k - 1) as nat,
    {
        let ptr_after = ptr_before.update(ans_j, ans_i + 1);
        assert forall|j: int| 1 <= j < n implies Self::count_col_less(s, j, ans_i, ans_j)
            == ptr_after[j] - (if j == ans_j { 1int } else { 0int }) by {
            if j == ans_j {
                Self::lemma_count_col_less_self(s, ans_j, ans_i);
                assert(ptr_after[j] == ans_i + 1);
            } else {
                assert(ptr_after[j] == ptr_before[j]);
                assert(ptr_before[ans_j] <= ans_i < ans_j);
                assert forall|a: int| 0 <= a < ptr_before[j] implies #[trigger] Self::fraction_less(s, a, j, ans_i, ans_j) by {
                    assert(1 <= j < n && 0 <= a < ptr_before[j]);
                    assert(1 <= ans_j < n && ptr_before[ans_j] <= ans_i < ans_j);
                }
                assert(ans_i < ptr_after[ans_j]);
                assert forall|a: int| ptr_after[j] <= a < j implies !(#[trigger] Self::fraction_less(s, a, j, ans_i, ans_j)) by {
                    assert(1 <= ans_j < n && 0 <= ans_i < ptr_after[ans_j]);
                    assert(1 <= j < n && ptr_after[j] <= a < j);
                    assert(Self::fraction_less(s, ans_i, ans_j, a, j));
                }
                Self::lemma_count_col_less_threshold(s, j, ans_i, ans_j, ptr_before[j]);
            }
        }
        assert(ptr_after.len() == n);
        assert(forall|j: int| 1 <= j < n ==> #[trigger] ptr_after[j] >= 0);
        assert(ptr_after[ans_j] == ans_i + 1);
        assert(Self::count_cols_upto_from(s, ans_i, ans_j, 1, n) == Self::sum_ptr(ptr_after, 1, n) - 1) by {
            Self::lemma_cols_upto_eq_sum_from(s, ans_i, ans_j, ptr_after, 1, n, ans_j);
        }
        Self::lemma_cols_upto_from_eq(s, ans_i, ans_j, n);
        Self::lemma_count_fractions_less_col(s, ans_i, ans_j);
    }

    pub open spec fn count_cols_upto_from(s: Seq<i32>, num_idx: int, den_idx: int, lo: int, hi: int) -> int
        decreases hi - lo,
    {
        if hi <= lo {
            0
        } else {
            Self::count_cols_upto_from(s, num_idx, den_idx, lo, hi - 1)
                + Self::count_col_less(s, hi - 1, num_idx, den_idx) as int
        }
    }

    proof fn lemma_cols_upto_from_eq(s: Seq<i32>, num_idx: int, den_idx: int, hi: int)
        ensures
            Self::count_cols_upto(s, num_idx, den_idx, hi) == Self::count_cols_upto_from(s, num_idx, den_idx, 1, hi),
        decreases hi,
    {
        if hi <= 1 {
            assert(Self::count_cols_upto_from(s, num_idx, den_idx, 1, hi) == 0);
            if hi == 1 {
                assert(Self::count_cols_upto(s, num_idx, den_idx, 1)
                    == Self::count_col_less(s, 0, num_idx, den_idx) + Self::count_cols_upto(s, num_idx, den_idx, 0));
                assert(Self::count_col_less(s, 0, num_idx, den_idx) == Self::count_col_less_from(s, 0, 0, num_idx, den_idx));
                assert(Self::count_col_less_from(s, 0, 0, num_idx, den_idx) == 0nat);
            }
        } else {
            Self::lemma_cols_upto_from_eq(s, num_idx, den_idx, hi - 1);
            assert(Self::count_cols_upto(s, num_idx, den_idx, hi)
                == Self::count_col_less(s, hi - 1, num_idx, den_idx) + Self::count_cols_upto(s, num_idx, den_idx, hi - 1));
            assert(Self::count_cols_upto_from(s, num_idx, den_idx, 1, hi)
                == Self::count_cols_upto_from(s, num_idx, den_idx, 1, hi - 1)
                    + Self::count_col_less(s, hi - 1, num_idx, den_idx) as int);
        }
    }

    proof fn lemma_cols_upto_eq_sum_from(s: Seq<i32>, ans_i: int, ans_j: int, ptr_after: Seq<int>, lo: int, hi: int, ans_j2: int)
        requires
            1 <= lo <= hi <= ptr_after.len(),
            lo <= ans_j2 < hi,
            forall|j: int| lo <= j < hi ==> #[trigger] ptr_after[j] >= 0,
            ptr_after[ans_j2] >= 1,
            forall|j: int| lo <= j < hi ==> #[trigger] Self::count_col_less(s, j, ans_i, ans_j)
                == ptr_after[j] - (if j == ans_j2 { 1int } else { 0int }),
        ensures
            Self::count_cols_upto_from(s, ans_i, ans_j, lo, hi) == Self::sum_ptr(ptr_after, lo, hi) - 1,
        decreases hi - lo,
    {
        if hi > lo {
            assert(Self::count_cols_upto_from(s, ans_i, ans_j, lo, hi)
                == Self::count_cols_upto_from(s, ans_i, ans_j, lo, hi - 1)
                    + Self::count_col_less(s, hi - 1, ans_i, ans_j) as int);
            assert(Self::sum_ptr(ptr_after, lo, hi) == Self::sum_ptr(ptr_after, lo, hi - 1) + ptr_after[hi - 1]);
            if hi - 1 == ans_j2 {
                assert(ptr_after[hi - 1] >= 1);
                assert(Self::count_col_less(s, hi - 1, ans_i, ans_j) == (ptr_after[hi - 1] - 1) as nat);
                assert(Self::count_col_less(s, hi - 1, ans_i, ans_j) as int == ptr_after[hi - 1] - 1);
                if hi - 1 > lo {
                    Self::lemma_cols_upto_eq_sum_from2(s, ans_i, ans_j, ptr_after, lo, hi - 1);
                } else {
                    assert(Self::count_cols_upto_from(s, ans_i, ans_j, lo, hi - 1) == 0);
                    assert(Self::sum_ptr(ptr_after, lo, hi - 1) == 0);
                }
            } else {
                Self::lemma_cols_upto_eq_sum_from(s, ans_i, ans_j, ptr_after, lo, hi - 1, ans_j2);
                assert(ptr_after[hi - 1] >= 0);
                assert(Self::count_col_less(s, hi - 1, ans_i, ans_j) == ptr_after[hi - 1] as nat);
                assert(Self::count_col_less(s, hi - 1, ans_i, ans_j) as int == ptr_after[hi - 1]);
            }
        }
    }

    proof fn lemma_cols_upto_eq_sum_from2(s: Seq<i32>, ans_i: int, ans_j: int, ptr_after: Seq<int>, lo: int, hi: int)
        requires
            1 <= lo <= hi <= ptr_after.len(),
            forall|j: int| lo <= j < hi ==> #[trigger] ptr_after[j] >= 0,
            forall|j: int| lo <= j < hi ==> #[trigger] Self::count_col_less(s, j, ans_i, ans_j) == ptr_after[j] as nat,
        ensures
            Self::count_cols_upto_from(s, ans_i, ans_j, lo, hi) == Self::sum_ptr(ptr_after, lo, hi),
        decreases hi - lo,
    {
        if hi > lo {
            Self::lemma_cols_upto_eq_sum_from2(s, ans_i, ans_j, ptr_after, lo, hi - 1);
            assert(Self::count_cols_upto_from(s, ans_i, ans_j, lo, hi)
                == Self::count_cols_upto_from(s, ans_i, ans_j, lo, hi - 1)
                    + Self::count_col_less(s, hi - 1, ans_i, ans_j) as int);
            assert(Self::sum_ptr(ptr_after, lo, hi) == Self::sum_ptr(ptr_after, lo, hi - 1) + ptr_after[hi - 1]);
            assert(ptr_after[hi - 1] >= 0);
            assert(Self::count_col_less(s, hi - 1, ans_i, ans_j) == ptr_after[hi - 1] as nat);
            assert(Self::count_col_less(s, hi - 1, ans_i, ans_j) as int == ptr_after[hi - 1]);
        }
    }

    proof fn lemma_sum_ptr_max(ptr: Seq<int>, n: int)
        requires
            1 <= n <= ptr.len(),
            forall|j: int| 1 <= j < n ==> 0 <= #[trigger] ptr[j] <= j,
        ensures
            Self::sum_ptr(ptr, 1, n) <= n * (n - 1) / 2,
        decreases n,
    {
        if n > 1 {
            Self::lemma_sum_ptr_max(ptr, n - 1);
            assert(Self::sum_ptr(ptr, 1, n) == Self::sum_ptr(ptr, 1, n - 1) + ptr[n - 1]);
            assert((n - 1) * (n - 2) / 2 + (n - 1) == n * (n - 1) / 2) by (nonlinear_arith);
        }
    }

    proof fn lemma_exists_valid_column(ptr: Seq<int>, n: int)
        requires
            1 <= n <= ptr.len(),
            forall|j: int| 1 <= j < n ==> 0 <= #[trigger] ptr[j] <= j,
            Self::sum_ptr(ptr, 1, n) < n * (n - 1) / 2,
        ensures
            exists|j: int| 1 <= j < n && #[trigger] ptr[j] < j,
        decreases n,
    {
        if n == 1 {
            assert(Self::sum_ptr(ptr, 1, 1) == 0);
            assert(n * (n - 1) / 2 == 0) by (nonlinear_arith)
                requires
                    n == 1,
            {
            }
            assert(false);
        } else {
            if ptr[n - 1] < n - 1 {
                assert(1 <= n - 1 < n && ptr[n - 1] < n - 1);
            } else {
                assert(ptr[n - 1] == n - 1);
                assert(Self::sum_ptr(ptr, 1, n) == Self::sum_ptr(ptr, 1, n - 1) + ptr[n - 1]);
                assert((n - 1) * (n - 2) / 2 + (n - 1) == n * (n - 1) / 2) by (nonlinear_arith);
                assert(Self::sum_ptr(ptr, 1, n - 1) < (n - 1) * (n - 2) / 2);
                Self::lemma_exists_valid_column(ptr, n - 1);
                let j0 = choose|j: int| 1 <= j < n - 1 && #[trigger] ptr[j] < j;
                assert(1 <= j0 < n && ptr[j0] < j0);
            }
        }
    }

    pub open spec fn ptr_view(ptr: Seq<usize>) -> Seq<int> {
        ptr.map(|_i: int, x: usize| x as int)
    }

    proof fn lemma_sum_ptr_zero(ptr: Seq<int>, n: int)
        requires
            forall|j: int| 1 <= j < n ==> #[trigger] ptr[j] == 0,
        ensures
            Self::sum_ptr(ptr, 1, n) == 0,
        decreases n,
    {
        if n > 1 {
            Self::lemma_sum_ptr_zero(ptr, n - 1);
        }
    }

    proof fn lemma_sum_ptr_unaffected(ptr: Seq<int>, hi: int, j: int, newv: int, lo: int)
        requires
            0 <= lo <= hi <= ptr.len(),
            0 <= j < ptr.len(),
            !(lo <= j < hi),
        ensures
            Self::sum_ptr(ptr.update(j, newv), lo, hi) == Self::sum_ptr(ptr, lo, hi),
        decreases hi - lo,
    {
        if hi > lo {
            Self::lemma_sum_ptr_unaffected(ptr, hi - 1, j, newv, lo);
            if j < lo {
                assert(j < lo <= hi - 1);
                assert(hi - 1 != j);
            } else {
                assert(j >= hi);
                assert(hi - 1 != j);
            }
            assert(ptr.update(j, newv)[hi - 1] == ptr[hi - 1]);
        }
    }

    proof fn lemma_sum_ptr_set(ptr: Seq<int>, n: int, j: int, newv: int)
        requires
            1 <= j < n <= ptr.len(),
        ensures
            Self::sum_ptr(ptr.update(j, newv), 1, n) == Self::sum_ptr(ptr, 1, n) - ptr[j] + newv,
        decreases n,
    {
        if n == j + 1 {
            assert(Self::sum_ptr(ptr.update(j, newv), 1, n)
                == Self::sum_ptr(ptr.update(j, newv), 1, n - 1) + ptr.update(j, newv)[n - 1]);
            assert(ptr.update(j, newv)[n - 1] == newv);
            assert(Self::sum_ptr(ptr, 1, n) == Self::sum_ptr(ptr, 1, n - 1) + ptr[n - 1]);
            Self::lemma_sum_ptr_unaffected(ptr, n - 1, j, newv, 1);
        } else {
            Self::lemma_sum_ptr_set(ptr, n - 1, j, newv);
            assert(Self::sum_ptr(ptr.update(j, newv), 1, n)
                == Self::sum_ptr(ptr.update(j, newv), 1, n - 1) + ptr.update(j, newv)[n - 1]);
            assert(ptr.update(j, newv)[n - 1] == ptr[n - 1]);
            assert(Self::sum_ptr(ptr, 1, n) == Self::sum_ptr(ptr, 1, n - 1) + ptr[n - 1]);
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
        let mut ptr: Vec<usize> = Vec::with_capacity(n);
        let mut idx: usize = 0;
        while idx < n
            invariant
                ptr.len() == idx,
                idx <= n,
                forall|i: int| 0 <= i < idx as int ==> #[trigger] ptr@[i] == 0,
            decreases n - idx,
        {
            ptr.push(0);
            idx += 1;
        }

        let mut ans_i: usize = 0;
        let mut ans_j: usize = 1;
        let ghost mut prev_ptr: Seq<int> = Self::ptr_view(ptr@);

        proof {
            assert(forall|j: int| 1 <= j < n as int ==> #[trigger] Self::ptr_view(ptr@)[j] == 0);
            assert forall|j1: int, a1: int, j2: int, a2: int|
                (1 <= j1 < n as int && 0 <= a1 < Self::ptr_view(ptr@)[j1])
                    && (1 <= j2 < n as int && Self::ptr_view(ptr@)[j2] <= a2 < j2)
                implies #[trigger] Self::fraction_less(arr@, a1, j1, a2, j2) by {
                assert(Self::ptr_view(ptr@)[j1] == 0);
                assert(false);
            }
            assert(Self::order_consistent(arr@, Self::ptr_view(ptr@), n as int));
            assert(Self::sum_ptr(Self::ptr_view(ptr@), 1, n as int) == 0) by {
                Self::lemma_sum_ptr_zero(Self::ptr_view(ptr@), n as int);
            }
        }

        let mut t: i32 = 0;
        while t < k
            invariant
                ptr.len() == n,
                2 <= n <= 1000,
                forall|i: int| 0 <= i < n ==> 1 <= #[trigger] arr@[i] <= 30_000,
                arr@[0] == 1,
                forall|i: int| 1 <= i < n ==> #[trigger] Self::is_prime(arr@[i] as int),
                forall|i: int, j: int| 0 <= i < j < n ==> arr@[i] < arr@[j],
                forall|j: int| 1 <= j < n as int ==> 0 <= #[trigger] Self::ptr_view(ptr@)[j] <= j,
                Self::order_consistent(arr@, Self::ptr_view(ptr@), n as int),
                Self::sum_ptr(Self::ptr_view(ptr@), 1, n as int) == t as int,
                0 <= t <= k,
                (k as int) <= (n as int) * (n as int - 1) / 2,
                1 <= ans_j < n,
                ans_i < ans_j,
                prev_ptr.len() == n as int,
                ans_i as int == prev_ptr[ans_j as int],
                forall|j: int| 1 <= j < n as int ==> 0 <= #[trigger] prev_ptr[j] <= j,
                Self::order_consistent(arr@, prev_ptr, n as int),
                t > 0 ==> Self::ptr_view(ptr@) == prev_ptr.update(ans_j as int, ans_i as int + 1),
            decreases k - t,
        {
            let ghost cur_ptr_seq = Self::ptr_view(ptr@);
            proof {
                assert(Self::sum_ptr(cur_ptr_seq, 1, n as int) < (n as int) * (n as int - 1) / 2);
                Self::lemma_exists_valid_column(cur_ptr_seq, n as int);
            }

            let mut best_j: usize = 0;
            let mut j: usize = 1;
            while j < n
                invariant
                    1 <= j <= n,
                    best_j == 0 || (1 <= (best_j as int) && (best_j as int) < (j as int) && (ptr@[best_j as int] as int) < (best_j as int)),
                    best_j != 0 ==> forall|j2: int|
                        1 <= j2 < j as int && #[trigger] cur_ptr_seq[j2] < j2
                        ==> !Self::fraction_less(arr@, cur_ptr_seq[j2], j2, cur_ptr_seq[best_j as int], best_j as int),
                    best_j == 0 ==> forall|j2: int| 1 <= j2 < j as int ==> #[trigger] cur_ptr_seq[j2] >= j2,
                    forall|i: int| 0 <= i < n as int ==> ptr@[i] as int == cur_ptr_seq[i],
                decreases n - j,
            {
                if ptr[j] < j {
                    let take = if best_j == 0 {
                        true
                    } else {
                        proof {
                            assert(1 <= arr@[(ptr@[j as int] as int)] <= 30_000);
                            assert(1 <= arr@[best_j as int] <= 30_000);
                            assert(1 <= arr@[(ptr@[best_j as int] as int)] <= 30_000);
                            assert(1 <= arr@[j as int] <= 30_000);
                            assert((arr@[(ptr@[j as int] as int)] as int) * (arr@[best_j as int] as int) <= 900_000_000) by (nonlinear_arith)
                                requires
                                    1 <= arr@[(ptr@[j as int] as int)] <= 30_000,
                                    1 <= arr@[best_j as int] <= 30_000,
                            {
                            }
                            assert((arr@[(ptr@[best_j as int] as int)] as int) * (arr@[j as int] as int) <= 900_000_000) by (nonlinear_arith)
                                requires
                                    1 <= arr@[(ptr@[best_j as int] as int)] <= 30_000,
                                    1 <= arr@[j as int] <= 30_000,
                            {
                            }
                        }
                        (arr[ptr[j]] as i64) * (arr[best_j] as i64) < (arr[ptr[best_j]] as i64) * (arr[j] as i64)
                    };
                    if take {
                        let ghost old_best_j = best_j;
                        proof {
                            if old_best_j != 0 {
                                assert forall|j2: int|
                                    1 <= j2 < j as int && #[trigger] cur_ptr_seq[j2] < j2
                                    implies !Self::fraction_less(arr@, cur_ptr_seq[j2], j2, cur_ptr_seq[j as int], j as int) by {
                                    assert(!Self::fraction_less(arr@, cur_ptr_seq[j2], j2, cur_ptr_seq[old_best_j as int], old_best_j as int));
                                    assert(Self::fraction_less(arr@, cur_ptr_seq[j as int], j as int, cur_ptr_seq[old_best_j as int], old_best_j as int));
                                    assert(1 <= arr@[cur_ptr_seq[j2]] <= 30_000);
                                    assert(1 <= arr@[j2] <= 30_000);
                                    assert(1 <= arr@[cur_ptr_seq[old_best_j as int]] <= 30_000);
                                    assert(1 <= arr@[old_best_j as int] <= 30_000);
                                    assert(1 <= arr@[cur_ptr_seq[j as int]] <= 30_000);
                                    assert(1 <= arr@[j as int] <= 30_000);
                                    Self::lemma_fraction_less_trans(
                                        arr@,
                                        cur_ptr_seq[j as int], j as int,
                                        cur_ptr_seq[old_best_j as int], old_best_j as int,
                                        cur_ptr_seq[j2], j2,
                                    );
                                    assert(Self::fraction_less(arr@, cur_ptr_seq[j as int], j as int, cur_ptr_seq[j2], j2));
                                    assert(!Self::fraction_less(arr@, cur_ptr_seq[j2], j2, cur_ptr_seq[j as int], j as int));
                                }
                            }
                        }
                        best_j = j;
                    }
                }
                j += 1;
            }

            proof {
                if best_j == 0 {
                    assert(forall|j2: int| 1 <= j2 < n as int ==> #[trigger] cur_ptr_seq[j2] >= j2);
                    let w = choose|w: int| 1 <= w < n as int && #[trigger] cur_ptr_seq[w] < w;
                    assert(false);
                }
            }

            ans_i = ptr[best_j];
            ans_j = best_j;
            ptr[best_j] = ptr[best_j] + 1;

            proof {
                assert(forall|j2: int|
                    (1 <= j2 < n as int && cur_ptr_seq[j2] < j2)
                        ==> !#[trigger] Self::fraction_less(arr@, cur_ptr_seq[j2], j2, cur_ptr_seq[best_j as int], best_j as int));
                Self::lemma_order_consistent_step(arr@, cur_ptr_seq, n as int, best_j as int);
                assert(Self::ptr_view(ptr@) == cur_ptr_seq.update(best_j as int, ans_i as int + 1));
                Self::lemma_sum_ptr_set(cur_ptr_seq, n as int, best_j as int, ans_i as int + 1);
                prev_ptr = cur_ptr_seq;
                assert(Self::ptr_view(ptr@) == prev_ptr.update(ans_j as int, ans_i as int + 1));
            }
            t += 1;
        }

        proof {
            assert(Self::ptr_view(ptr@) == prev_ptr.update(ans_j as int, ans_i as int + 1));
            assert(Self::order_consistent(arr@, prev_ptr.update(ans_j as int, ans_i as int + 1), n as int));
            assert(Self::sum_ptr(prev_ptr.update(ans_j as int, ans_i as int + 1), 1, n as int) == k as int);
            Self::lemma_final_count(arr@, n as int, prev_ptr, ans_i as int, ans_j as int, k as int);
        }

        let mut result = Vec::new();
        result.push(arr[ans_i]);
        result.push(arr[ans_j]);
        result
    }
}

}
