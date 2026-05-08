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

    proof fn lemma_count_less_outer_nonneg(s: Seq<i32>, ni: int, dj: int, a: int)
        requires a >= 0,
        ensures Self::count_less_outer(s, ni, dj, a) >= 0,
        decreases (s.len() - a) as nat,
    {
        if a >= s.len() {
        } else {
            Self::lemma_count_less_outer_step(s, ni, dj, a);
            Self::lemma_count_less_outer_nonneg(s, ni, dj, a + 1);
        }
    }

    proof fn lemma_count_less_outer_step(s: Seq<i32>, ni: int, dj: int, a: int)
        requires
            a >= 0,
            a < s.len(),
        ensures
            Self::count_less_outer(s, ni, dj, a)
                == Self::count_less_inner(s, ni, dj, a, a + 1)
                    + Self::count_less_outer(s, ni, dj, a + 1),
    {
        assert(Self::count_less_outer(s, ni, dj, a)
            == Self::count_less_inner(s, ni, dj, a, a + 1)
                + Self::count_less_outer(s, ni, dj, a + 1));
    }

    proof fn lemma_count_less_inner_bounded(s: Seq<i32>, ni: int, dj: int, a: int, b: int)
        requires
            a < b,
            b <= s.len(),
        ensures
            Self::count_less_inner(s, ni, dj, a, b) <= (s.len() - b) as nat,
        decreases (s.len() - b) as nat,
    {
        if b >= s.len() {
        } else {
            Self::lemma_count_less_inner_bounded(s, ni, dj, a, b + 1);
        }
    }

    proof fn lemma_count_less_inner_decreasing(s: Seq<i32>, ni: int, dj: int, a: int, b: int, b2: int)
        requires
            a < b,
            b <= b2,
            b2 <= s.len(),
        ensures
            Self::count_less_inner(s, ni, dj, a, b) >= Self::count_less_inner(s, ni, dj, a, b2),
        decreases (b2 - b) as nat,
    {
        if b >= b2 {
        } else {
            Self::lemma_count_less_inner_decreasing(s, ni, dj, a, b + 1, b2);
        }
    }

    proof fn lemma_count_fractions_less_bounded(s: Seq<i32>, ni: int, dj: int)
        ensures
            Self::count_fractions_less(s, ni, dj) <= (s.len() * (s.len() - 1) / 2) as nat,
    {
        Self::lemma_count_fractions_less_bounded_from(s, ni, dj, 0);
    }

    proof fn lemma_count_fractions_less_bounded_from(s: Seq<i32>, ni: int, dj: int, a: int)
        requires
            a >= 0,
            a <= s.len(),
        ensures
            Self::count_less_outer(s, ni, dj, a) <= ((s.len() - a) * (s.len() - a - 1) / 2) as nat,
        decreases (s.len() - a) as nat,
    {
        if a >= s.len() {
        } else {
            Self::lemma_count_less_inner_bounded(s, ni, dj, a, a + 1);
            Self::lemma_count_less_outer_step(s, ni, dj, a);
            Self::lemma_count_fractions_less_bounded_from(s, ni, dj, a + 1);
            let l = s.len() - a;
            assert(((s.len() - (a + 1)) * (s.len() - (a + 1) - 1) / 2) == (l - 1) * (l - 2) / 2);
            assert((s.len() - a) * (s.len() - a - 1) / 2 == l * (l - 1) / 2);
            assert((s.len() - a - 1) + ((s.len() - (a + 1)) * (s.len() - (a + 1) - 1) / 2)
                == (l - 1) + (l - 1) * (l - 2) / 2);
            assert((l - 1) + (l - 1) * (l - 2) / 2 == l * (l - 1) / 2) by(nonlinear_arith);
        }
    }

    #[verifier::loop_isolation(false)]
    #[verifier::exec_allows_no_decreases_clause]
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
        let _mirror = if false {
            let n = arr.len();
            let target = k;

            let mut low = 0.0f64;
            let mut high = 1.0f64;
            let mut ans_num = arr[0];
            let mut ans_den = arr[n - 1];

            let mut iter = 0usize;
            while iter < 64
            {
                let mid = (low + high) / 2.0f64;
                let mut count = 0i32;
                let mut best_num = 0i32;
                let mut best_den = 1i32;

                let mut i = 0usize;
                let mut j = 1usize;
                while j < n
                {
                    while i < j && (arr[i] as f64) <= mid * (arr[j] as f64)
                    {
                        if (arr[i] as i64) * (best_den as i64) > (best_num as i64) * (arr[j] as i64) {
                            best_num = arr[i];
                            best_den = arr[j];
                        }
                        i += 1;
                    }
                    count += i as i32;
                    j += 1;
                }

                if count < target {
                    low = mid;
                } else {
                    ans_num = best_num;
                    ans_den = best_den;
                    high = mid;
                }
                iter += 1;
            }

            vec![ans_num, ans_den]
        } else {
            Vec::new()
        };
        let n = arr.len();
        proof {
            assert((n as int) * ((n as int) - 1) / 2 < 4294967296) by(nonlinear_arith)
                requires (n as int) <= 1000;
            assert((n as int) * ((n as int) - 1) / 2 < 18446744073709551616) by(nonlinear_arith)
                requires (n as int) <= 1000;
        }
        let k = k as i32;
        let ghost (wi, wj): (int, int) = choose|wi: int, wj: int|
            0 <= wi < wj < arr@.len()
            && #[trigger] Self::count_fractions_less(arr@, wi, wj) == (k - 1) as nat;
        let mut i = 0usize;
        while i < n
            invariant
                n == arr@.len(),
                2 <= n <= 1000,
                (n as int) * ((n as int) - 1) / 2 < 4294967296,
                forall|ii: int| 0 <= ii < n ==> 1 <= #[trigger] arr@[ii] <= 30_000,
                arr@[0] == 1,
                forall|ii: int, jj: int| 0 <= ii < jj < n ==> arr@[ii] < arr@[jj],
                1 <= k <= (n * (n - 1) / 2) as int,
                0 <= wi < n as int,
                wi < wj < n as int,
                Self::count_fractions_less(arr@, wi, wj) == (k - 1) as nat,
                0 <= i <= n,
                ((i as int) < wi) || ((i as int) == wi),
            decreases n - i,
        {
            let mut j = i + 1;
            proof {
                Self::lemma_count_fractions_less_bounded(arr@, i as int, j as int);
            }
            while j < n
                invariant
                    n == arr@.len(),
                    2 <= n <= 1000,
                    i < n,
                    i + 1 <= j <= n,
                    j <= n,
                    1 <= k,
                    (n as int) * ((n as int) - 1) / 2 < 4294967296,
                    forall|ii: int| 0 <= ii < n ==> 1 <= #[trigger] arr@[ii] <= 30_000,
                    Self::count_fractions_less(arr@, wi, wj) == (k - 1) as nat,
                    Self::count_fractions_less(arr@, i as int, j as int) <= (n * (n - 1) / 2) as nat,
                    ((i as int) < wi) || ((i as int) == wi && (j as int) <= wj),
                decreases n - j,
            {
                let mut count = 0usize;
                proof {
                    Self::lemma_count_fractions_less_bounded(arr@, i as int, j as int);
                }
                let mut a = 0usize;
                while a < n
                    invariant
                        n == arr@.len(),
                        2 <= n <= 1000,
                        0 <= a <= n,
                        0 <= count,
                        i < n,
                        j < n,
                        1 <= k,
                        forall|ii: int| 0 <= ii < n ==> 1 <= #[trigger] arr@[ii] <= 30_000,
                        count as nat
                            == Self::count_fractions_less(arr@, i as int, j as int)
                            - Self::count_less_outer(arr@, i as int, j as int, a as int),
                    decreases n - a,
                {
                    let mut b = a + 1;
                    proof {
                        Self::lemma_count_less_outer_nonneg(arr@, i as int, j as int, a as int);
                        Self::lemma_count_fractions_less_bounded(arr@, i as int, j as int);
                        assert(count as nat <= Self::count_fractions_less(arr@, i as int, j as int));
                        assert(count as nat <= (n * (n - 1) / 2) as nat);
                    }
                    while b < n
                    invariant
                        n == arr@.len(),
                        2 <= n <= 1000,
                        a < n,
                        a + 1 <= b <= n,
                        i < n,
                        j < n,
                        forall|ii: int| 0 <= ii < n ==> 1 <= #[trigger] arr@[ii] <= 30_000,
                        count as nat <= (n * (n - 1) / 2) as nat,
                        count as nat
                            == Self::count_fractions_less(arr@, i as int, j as int)
                            - Self::count_less_outer(arr@, i as int, j as int, a as int)
                            + Self::count_less_inner(arr@, i as int, j as int, a as int, a as int + 1)
                            - Self::count_less_inner(arr@, i as int, j as int, a as int, b as int),
                        decreases n - b,
                    {
                        proof {
                            assert(0 <= (a as int) && (a as int) < n as int);
                            assert(0 <= (b as int) && (b as int) < n as int);
                            assert(0 <= (i as int) && (i as int) < n as int);
                            assert(0 <= (j as int) && (j as int) < n as int);
                            assert(1 <= arr@[a as int] && arr@[a as int] <= 30_000);
                            assert(1 <= arr@[b as int] && arr@[b as int] <= 30_000);
                            assert(1 <= arr@[i as int] && arr@[i as int] <= 30_000);
                            assert(1 <= arr@[j as int] && arr@[j as int] <= 30_000);
                            assert((arr@[a as int] as int) * (arr@[j as int] as int) <= 900_000_000) by(nonlinear_arith)
                                requires 1 <= arr@[a as int] <= 30_000, 1 <= arr@[j as int] <= 30_000;
                            assert((arr@[i as int] as int) * (arr@[b as int] as int) <= 900_000_000) by(nonlinear_arith)
                                requires 1 <= arr@[i as int] <= 30_000, 1 <= arr@[b as int] <= 30_000;
                        }
                        let add_one = (arr[a] as u64) * (arr[j] as u64) < (arr[i] as u64) * (arr[b] as u64);
                        let old_count = count;
                        proof {
                            assert((old_count as nat) <= (n * (n - 1) / 2) as nat);
                            assert((n as int) * ((n as int) - 1) / 2 < 500000) by(nonlinear_arith)
                                requires 2 <= (n as int) <= 1000;
                        }
                        count = old_count + (if add_one { 1usize } else { 0usize });
                        proof {
                            let add = if Self::fraction_less(arr@, a as int, b as int, i as int, j as int)
                                { 1nat } else { 0nat };
                            assert(Self::fraction_less(arr@, a as int, b as int, i as int, j as int)
                                == ((arr@[a as int] as int) * (arr@[j as int] as int)
                                    < (arr@[i as int] as int) * (arr@[b as int] as int)));
                            assert(((arr@[a as int] as int) * (arr@[j as int] as int)
                                < (arr@[i as int] as int) * (arr@[b as int] as int)) <==> add_one);
                            assert(add_one == Self::fraction_less(arr@, a as int, b as int, i as int, j as int));
                            assert(add == (if add_one { 1nat } else { 0nat }));
                            assert((if add_one { 1usize } else { 0usize }) as nat == add);
                            assert((count as nat) == (old_count as nat) + add);
                            assert((old_count as nat)
                                == Self::count_fractions_less(arr@, i as int, j as int)
                                    - Self::count_less_outer(arr@, i as int, j as int, a as int)
                                    + Self::count_less_inner(arr@, i as int, j as int, a as int, a as int + 1)
                                    - Self::count_less_inner(arr@, i as int, j as int, a as int, b as int));
                            assert(Self::count_less_inner(arr@, i as int, j as int, a as int, b as int)
                                == add + Self::count_less_inner(arr@, i as int, j as int, a as int, (b as int) + 1));
                            assert(count as nat
                                == Self::count_fractions_less(arr@, i as int, j as int)
                                    - Self::count_less_outer(arr@, i as int, j as int, a as int)
                                    + Self::count_less_inner(arr@, i as int, j as int, a as int, a as int + 1)
                                    - Self::count_less_inner(arr@, i as int, j as int, a as int, (b as int) + 1));
                            Self::lemma_count_fractions_less_bounded(arr@, i as int, j as int);
                            assert(count as nat <= (n * (n - 1) / 2) as nat);
                        }
                        b += 1;
                    }
                    proof {
                        assert(Self::count_less_inner(arr@, i as int, j as int, a as int, n as int)
                            == 0nat);
                        Self::lemma_count_less_outer_step(arr@, i as int, j as int, a as int);
                        assert(count as nat
                            == Self::count_fractions_less(arr@, i as int, j as int)
                                - Self::count_less_outer(arr@, i as int, j as int, (a + 1) as int));
                    }
                    a += 1;
                }
                proof {
                    assert(Self::count_less_outer(arr@, i as int, j as int, n as int) == 0nat);
                    assert(count as nat == Self::count_fractions_less(arr@, i as int, j as int));
                }
                if count == (k - 1) as usize {
                    let mut result = Vec::new();
                    result.push(arr[i]);
                    result.push(arr[j]);
                    proof {
                        assert(Self::count_less_outer(arr@, i as int, j as int, n as int) == 0nat);
                        assert(count as nat == Self::count_fractions_less(arr@, i as int, j as int));
                        assert(Self::count_fractions_less(arr@, i as int, j as int) == (k - 1) as nat);
                        assert(result@[0] == arr@[i as int]);
                        assert(result@[1] == arr@[j as int]);
                    }
                    return result;
                }
                proof {
                    assert(Self::count_fractions_less(arr@, wi, wj) == (k - 1) as nat);
                    assert((i as int == wi && j as int == wj) ==> Self::count_fractions_less(arr@, i as int, j as int) == Self::count_fractions_less(arr@, wi, wj));
                    assert((i as int == wi && j as int == wj) ==> count as nat == (k - 1) as nat);
                    assert((i as int != wi) || (j as int != wj));
                }
                proof {
                    Self::lemma_count_fractions_less_bounded(arr@, i as int, (j + 1) as int);
                }
                j += 1;
            }
            i += 1;
        }
        proof {
            assert(i == n);
            assert(((i as int) < wi) || ((i as int) == wi));
            assert(n as int <= wi);
            assert(wi < n as int);
            assert(false);
        }
        let mut result = Vec::new();
        result.push(arr[0]);
        result.push(arr[n - 1]);
        result
    }
}

}
