use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn abs_diff(a: int, b: int) -> int {
        if a >= b { a - b } else { b - a }
    }

    pub open spec fn dp(locs: Seq<i32>, n: int, city: int, finish: int, fuel: int, j: int) -> int
        decreases fuel, n - j,
    {
        if fuel < 0 {
            0int
        } else if j >= n {
            if city == finish { 1int } else { 0int }
        } else if j == city {
            Self::dp(locs, n, city, finish, fuel, j + 1)
        } else {
            let cost = Self::abs_diff(locs[city] as int, locs[j] as int);
            if cost >= 1 && cost <= fuel {
                Self::dp(locs, n, j, finish, fuel - cost, 0)
                    + Self::dp(locs, n, city, finish, fuel, j + 1)
            } else {
                Self::dp(locs, n, city, finish, fuel, j + 1)
            }
        }
    }

    proof fn lemma_dp_nonneg(locs: Seq<i32>, n: int, city: int, finish: int, fuel: int, j: int)
        requires
            0 <= j <= n,
            n >= 1,
        ensures
            Self::dp(locs, n, city, finish, fuel, j) >= 0,
        decreases fuel, n - j,
    {
        if fuel < 0 {
        } else if j >= n {
        } else if j == city {
            Self::lemma_dp_nonneg(locs, n, city, finish, fuel, j + 1);
        } else {
            let cost = Self::abs_diff(locs[city] as int, locs[j] as int);
            if cost >= 1 && cost <= fuel {
                Self::lemma_dp_nonneg(locs, n, j, finish, fuel - cost, 0);
                Self::lemma_dp_nonneg(locs, n, city, finish, fuel, j + 1);
            } else {
                Self::lemma_dp_nonneg(locs, n, city, finish, fuel, j + 1);
            }
        }
    }

    proof fn lemma_dp_mono_j(locs: Seq<i32>, n: int, city: int, finish: int, fuel: int, j: int)
        requires
            0 <= j < n,
            0 <= city < n,
            fuel >= 0,
            n >= 1,
        ensures
            Self::dp(locs, n, city, finish, fuel, j) >= Self::dp(locs, n, city, finish, fuel, j + 1),
    {
        if j == city {
        } else {
            let cost = Self::abs_diff(locs[city] as int, locs[j] as int);
            if cost >= 1 && cost <= fuel {
                Self::lemma_dp_nonneg(locs, n, j, finish, fuel - cost, 0);
            }
        }
    }

    proof fn lemma_dp_mono_j_range(locs: Seq<i32>, n: int, city: int, finish: int, fuel: int, j1: int, j2: int)
        requires
            0 <= j1 <= j2 <= n,
            0 <= city < n,
            fuel >= 0,
            n >= 1,
        ensures
            Self::dp(locs, n, city, finish, fuel, j1) >= Self::dp(locs, n, city, finish, fuel, j2),
        decreases j2 - j1,
    {
        if j1 < j2 {
            Self::lemma_dp_mono_j(locs, n, city, finish, fuel, j2 - 1);
            Self::lemma_dp_mono_j_range(locs, n, city, finish, fuel, j1, j2 - 1);
        }
    }

    proof fn lemma_dp_fuel_zero(locs: Seq<i32>, n: int, city: int, finish: int, j: int)
        requires
            0 <= j <= n,
            0 <= city < n,
            0 <= finish < n,
            n == locs.len(),
            forall |a: int, b: int| #![trigger locs[a], locs[b]] 0 <= a && a < b && b < n ==> locs[a] != locs[b],
        ensures
            Self::dp(locs, n, city, finish, 0, j) == if city == finish { 1int } else { 0int },
        decreases n - j,
    {
        if j >= n {
        } else if j == city {
            Self::lemma_dp_fuel_zero(locs, n, city, finish, j + 1);
        } else {
            if city < j {
                assert(locs[city] != locs[j]);
            } else {
                assert(locs[j] != locs[city as int]);
            }
            assert(Self::abs_diff(locs[city] as int, locs[j] as int) >= 1);
            Self::lemma_dp_fuel_zero(locs, n, city, finish, j + 1);
        }
    }

    proof fn lemma_mod_add(a: int, b: int, m: int)
        requires
            a >= 0,
            b >= 0,
            m > 0,
        ensures
            (a % m + b % m) % m == (a + b) % m,
    {
        assert(a == m * (a / m) + a % m) by {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a, m);
        }
        assert(b == m * (b / m) + b % m) by {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(b, m);
        }
        assert(a + b == m * (a / m + b / m) + (a % m + b % m)) by (nonlinear_arith)
            requires
                a == m * (a / m) + a % m,
                b == m * (b / m) + b % m;
        vstd::arithmetic::div_mod::lemma_mod_multiples_vanish(a / m + b / m, a % m + b % m, m);
    }

    #[verifier::spinoff_prover]
    pub fn count_routes(locations: Vec<i32>, start: i32, finish: i32, fuel: i32) -> (result: i32)
        requires
            2 <= locations.len() <= 100,
            forall |i: int| 0 <= i < locations.len() ==> 1 <= #[trigger] locations[i] <= 1_000_000_000,
            forall |i: int, j: int| #![trigger locations[i], locations[j]] 0 <= i && i < j && j < locations.len() ==> locations[i] != locations[j],
            0 <= start < locations.len(),
            0 <= finish < locations.len(),
            1 <= fuel <= 200,
        ensures
            0 <= result < 1_000_000_007,
            result as int == Self::dp(
                locations@,
                locations.len() as int,
                start as int,
                finish as int,
                fuel as int,
                0int,
            ) % 1_000_000_007,
    {
        let n = locations.len();
        let fuel_cap: usize = (fuel as usize) + 1;
        proof {
            assert((n as int) * (fuel_cap as int) <= 20100) by (nonlinear_arith)
                requires n <= 100, fuel_cap <= 201;
        }
        let total_size: usize = n * fuel_cap;
        let modv: i64 = 1_000_000_007;
        let fi: usize = finish as usize;

        let ghost locs: Seq<i32> = locations@;
        let ghost n_int: int = n as int;
        let ghost finish_int: int = finish as int;
        let ghost MOD_INT: int = 1_000_000_007int;
        let ghost fc: int = fuel_cap as int;

        let mut dp: Vec<i64> = Vec::new();
        let mut idx: usize = 0;
        while idx < total_size
            invariant
                0 <= idx <= total_size,
                dp.len() == idx,
                total_size == n * fuel_cap,
                total_size <= 20100,
                forall |k: int| 0 <= k < idx as int ==> dp@[k] == 0i64,
            decreases total_size - idx,
        {
            dp.push(0i64);
            idx = idx + 1;
        }

        let mut bf: usize = 0;
        while bf < fuel_cap
            invariant
                0 <= bf <= fuel_cap,
                dp.len() == total_size,
                total_size == n * fuel_cap,
                total_size <= 20100,
                2 <= n <= 100,
                2 <= fuel_cap <= 201,
                0 <= fi < n,
                fc == fuel_cap as int,
                forall |fp: int| 0 <= fp < bf as int ==> #[trigger] dp@[fi as int * fc + fp] == 1i64,
                forall |k: int| 0 <= k < total_size as int
                    && !(fi as int * fc <= k < fi as int * fc + bf as int)
                    ==> dp@[k] == 0i64,
            decreases fuel_cap - bf,
        {
            proof {
                assert(fi * fuel_cap + bf < total_size) by (nonlinear_arith)
                    requires fi < n, bf < fuel_cap, total_size == n * fuel_cap, n >= 2, fuel_cap >= 2;
            }
            dp.set(fi * fuel_cap + bf, 1i64);
            bf = bf + 1;
        }

        proof {
            assert forall |i: int, fp: int| #![trigger dp@[i * fc + fp]] 0 <= i && i < n_int && 0 <= fp && fp < fc
                implies dp@[i * fc + fp] == (if i == finish_int { 1i64 } else { 0i64 })
            by {
                assert(0 <= i * (fuel_cap as int) + fp && i * (fuel_cap as int) + fp < total_size as int) by (nonlinear_arith)
                    requires 0 <= i, i < (n as int), 0 <= fp, fp < (fuel_cap as int),
                        total_size == n * fuel_cap,
                        n >= 2, fuel_cap >= 2;
                if i == finish_int {
                    assert(fi as int * fc <= i * fc + fp < fi as int * fc + fc);
                } else {
                    assert(!(fi as int * (fuel_cap as int) <= i * (fuel_cap as int) + fp
                        && i * (fuel_cap as int) + fp < fi as int * (fuel_cap as int) + (fuel_cap as int))) by (nonlinear_arith)
                        requires
                            i != fi as int, 0 <= i, i < (n as int), 0 <= fp, fp < (fuel_cap as int),
                            0 <= fi as int, (fi as int) < (n as int),
                            fuel_cap >= 2;
                }
            };

            assert forall |i: int| #![trigger dp@[i * fc]] 0 <= i < n_int
                implies {
                    &&& dp@[i * fc] as int
                        == Self::dp(locs, n_int, i, finish_int, 0, 0) % MOD_INT
                    &&& 0 <= dp@[i * fc] < modv
                }
            by {
                Self::lemma_dp_fuel_zero(locs, n_int, i, finish_int, 0);
                assert(0 <= i * fc && i * fc < total_size as int) by (nonlinear_arith)
                    requires 0 <= i, i < (n as int), total_size == n * fuel_cap, fuel_cap >= 2, n >= 2,
                        fc == (fuel_cap as int);
                
                assert(dp@[i * fc + 0int] == (if i == finish_int { 1i64 } else { 0i64 }));
                if i == finish_int {
                    assert(Self::dp(locs, n_int, i, finish_int, 0, 0) == 1int);
                    assert(dp@[i * fc] == 1i64);
                } else {
                    assert(Self::dp(locs, n_int, i, finish_int, 0, 0) == 0int);
                    assert(dp@[i * fc] == 0i64);
                }
            };
        }

        let mut f: usize = 1;
        while f < fuel_cap
            invariant
                1 <= f <= fuel_cap,
                dp.len() == total_size,
                total_size == n * fuel_cap,
                total_size <= 20100,
                2 <= n <= 100,
                2 <= fuel_cap <= 201,
                0 <= fi < n,
                modv == 1_000_000_007i64,
                locs == locations@,
                n_int == n as int,
                finish_int == finish as int,
                MOD_INT == 1_000_000_007int,
                fi == finish as usize,
                fc == fuel_cap as int,
                n == locations.len(),
                forall |i: int| 0 <= i < locations.len() ==> 1 <= #[trigger] locations[i] <= 1_000_000_000,
                forall |a: int, b: int| #![trigger locations[a], locations[b]] 0 <= a && a < b && b < locations.len() ==> locations[a] != locations[b],
                forall |i: int, fp: int| #![trigger dp@[i * fc + fp]] 0 <= i && i < n_int && 0 <= fp && fp < (f as int) ==> {
                    &&& dp@[i * fc + fp] as int
                        == Self::dp(locs, n_int, i, finish_int, fp, 0) % MOD_INT
                    &&& 0 <= dp@[i * fc + fp] < modv
                },
                forall |i: int, fp: int| #![trigger dp@[i * fc + fp]] 0 <= i && i < n_int && (f as int) <= fp && fp < fc ==>
                    dp@[i * fc + fp] == (if i == finish_int { 1i64 } else { 0i64 }),
            decreases fuel_cap - f,
        {
            let mut city: usize = 0;
            while city < n
                invariant
                    0 <= city <= n,
                    1 <= f < fuel_cap,
                    dp.len() == total_size,
                    total_size == n * fuel_cap,
                    total_size <= 20100,
                    2 <= n <= 100,
                    2 <= fuel_cap <= 201,
                    0 <= fi < n,
                    modv == 1_000_000_007i64,
                    locs == locations@,
                    n_int == n as int,
                    finish_int == finish as int,
                    MOD_INT == 1_000_000_007int,
                    fi == finish as usize,
                    fc == fuel_cap as int,
                    n == locations.len(),
                    forall |i: int| 0 <= i < locations.len() ==> 1 <= #[trigger] locations[i] <= 1_000_000_000,
                    forall |a: int, b: int| #![trigger locations[a], locations[b]] 0 <= a && a < b && b < locations.len() ==> locations[a] != locations[b],
                    forall |i: int, fp: int| #![trigger dp@[i * fc + fp]] 0 <= i && i < n_int && 0 <= fp && fp < (f as int) ==> {
                        &&& dp@[i * fc + fp] as int
                            == Self::dp(locs, n_int, i, finish_int, fp, 0) % MOD_INT
                        &&& 0 <= dp@[i * fc + fp] < modv
                    },
                    forall |i: int| #![trigger dp@[i * fc + f as int]] 0 <= i < city as int ==> {
                        &&& dp@[i * fc + f as int] as int
                            == Self::dp(locs, n_int, i, finish_int, f as int, 0) % MOD_INT
                        &&& 0 <= dp@[i * fc + f as int] < modv
                    },
                    forall |i: int| #![trigger dp@[i * fc + f as int]] (city as int) <= i && i < n_int ==>
                        dp@[i * fc + f as int] == (if i == finish_int { 1i64 } else { 0i64 }),
                    forall |i: int, fp: int| #![trigger dp@[i * fc + fp]]
                        0 <= i && i < n_int && (f as int) < fp && fp < fc ==>
                        dp@[i * fc + fp] == (if i == finish_int { 1i64 } else { 0i64 }),
                decreases n - city,
            {
                let ghost base_val: int = if city as int == finish_int { 1int } else { 0int };
                let ghost dp_total = Self::dp(locs, n_int, city as int, finish_int, f as int, 0);

                proof {
                    assert(dp@[city as int * fc + f as int] == base_val as i64);
                    Self::lemma_dp_nonneg(locs, n_int, city as int, finish_int, f as int, 0);
                    Self::lemma_dp_mono_j_range(locs, n_int, city as int, finish_int, f as int, 0, 0);
                    assert((dp_total + base_val - dp_total) % MOD_INT == base_val % MOD_INT);
                    assert(dp_total >= 0);
                    assert(base_val >= 0);
                }

                let mut j: usize = 0;
                while j < n
                    invariant
                        0 <= j <= n,
                        0 <= city < n,
                        1 <= f < fuel_cap,
                        dp.len() == total_size,
                        total_size == n * fuel_cap,
                        total_size <= 20100,
                        2 <= n <= 100,
                        2 <= fuel_cap <= 201,
                        0 <= fi < n,
                        modv == 1_000_000_007i64,
                        locs == locations@,
                        n_int == n as int,
                        finish_int == finish as int,
                        MOD_INT == 1_000_000_007int,
                        fi == finish as usize,
                        fc == fuel_cap as int,
                        n == locations.len(),
                        forall |i: int| 0 <= i < locations.len() ==> 1 <= #[trigger] locations[i] <= 1_000_000_000,
                        forall |a: int, b: int| #![trigger locations[a], locations[b]] 0 <= a && a < b && b < locations.len() ==> locations[a] != locations[b],
                        forall |i: int, fp: int| #![trigger dp@[i * fc + fp]] 0 <= i && i < n_int && 0 <= fp && fp < (f as int) ==> {
                            &&& dp@[i * fc + fp] as int
                                == Self::dp(locs, n_int, i, finish_int, fp, 0) % MOD_INT
                            &&& 0 <= dp@[i * fc + fp] < modv
                        },
                        dp@[city as int * fc + f as int] as int == (
                            Self::dp(locs, n_int, city as int, finish_int, f as int, 0)
                            + (if city as int == finish_int { 1int } else { 0int })
                            - Self::dp(locs, n_int, city as int, finish_int, f as int, j as int)
                        ) % MOD_INT,
                        0 <= dp@[city as int * fc + f as int] < modv,
                        Self::dp(locs, n_int, city as int, finish_int, f as int, 0)
                            + (if city as int == finish_int { 1int } else { 0int })
                            - Self::dp(locs, n_int, city as int, finish_int, f as int, j as int)
                            >= 0,
                        forall |i: int| #![trigger dp@[i * fc + f as int]] 0 <= i < city as int ==> {
                            &&& dp@[i * fc + f as int] as int
                                == Self::dp(locs, n_int, i, finish_int, f as int, 0) % MOD_INT
                            &&& 0 <= dp@[i * fc + f as int] < modv
                        },
                        forall |i: int| #![trigger dp@[i * fc + f as int]] (city as int) < i && i < n_int ==>
                            dp@[i * fc + f as int] == (if i == finish_int { 1i64 } else { 0i64 }),
                        forall |i: int, fp: int| #![trigger dp@[i * fc + fp]]
                            0 <= i && i < n_int && (f as int) < fp && fp < fc ==>
                            dp@[i * fc + fp] == (if i == finish_int { 1i64 } else { 0i64 }),
                    decreases n - j,
                {
                    if j != city {
                        let cost_val: usize = if locations[city] >= locations[j] {
                            (locations[city] - locations[j]) as usize
                        } else {
                            (locations[j] - locations[city]) as usize
                        };

                        proof {
                            assert(cost_val as int == Self::abs_diff(locs[city as int] as int, locs[j as int] as int));
                        }

                        if f >= cost_val {
                            proof {
                                let h_city = city as int;
                                let h_j = j as int;
                                let h_f = f as int;
                                let cost_spec = Self::abs_diff(locs[h_city] as int, locs[h_j] as int);
                                let bv: int = if h_city == finish_int { 1int } else { 0int };
                                let dp_t = Self::dp(locs, n_int, h_city, finish_int, h_f, 0);
                                let dp_j = Self::dp(locs, n_int, h_city, finish_int, h_f, h_j);
                                let dp_j1 = Self::dp(locs, n_int, h_city, finish_int, h_f, h_j + 1);
                                let dp_contrib = Self::dp(locs, n_int, h_j, finish_int, h_f - cost_spec, 0);

                                
                                if h_city < h_j {
                                    assert(locs[h_city] != locs[h_j]);
                                } else {
                                    assert(locs[h_j] != locs[h_city]);
                                }
                                assert(cost_spec >= 1);

                                assert(dp_j == dp_contrib + dp_j1);

                                Self::lemma_dp_nonneg(locs, n_int, h_j, finish_int, h_f - cost_spec, 0);
                                assert(dp_contrib >= 0);

                                let big_val = dp_t + bv - dp_j;
                                assert(big_val >= 0);

                                Self::lemma_mod_add(big_val, dp_contrib, MOD_INT);

                                assert(big_val + dp_contrib == dp_t + bv - dp_j1);

                                Self::lemma_dp_mono_j_range(locs, n_int, h_city, finish_int, h_f, 0, h_j + 1);
                                Self::lemma_dp_nonneg(locs, n_int, h_city, finish_int, h_f, 0);
                                assert(dp_t + bv - dp_j1 >= 0);

                                assert(dp@[h_j * fc + (h_f - cost_spec)] as int == dp_contrib % MOD_INT);

                                assert(dp@[h_city * fc + h_f] as int == big_val % MOD_INT);

                                assert((big_val % MOD_INT + dp_contrib % MOD_INT) % MOD_INT
                                    == (big_val + dp_contrib) % MOD_INT);

                                assert(0 <= big_val % MOD_INT < MOD_INT);
                                assert(0 <= dp_contrib % MOD_INT < MOD_INT);
                                assert(big_val % MOD_INT + dp_contrib % MOD_INT < 2 * MOD_INT);

                                assert(city * fuel_cap + f < total_size) by (nonlinear_arith)
                                    requires city < n, f < fuel_cap, total_size == n * fuel_cap, n >= 2;
                                assert(j * fuel_cap + (f - cost_val) < total_size) by (nonlinear_arith)
                                    requires j < n, f >= cost_val, f < fuel_cap, total_size == n * fuel_cap, n >= 2;
                                assert((city * fuel_cap + f) as int == city as int * fc + f as int) by (nonlinear_arith)
                                    requires fc == fuel_cap as int, fuel_cap <= 201, city <= 100, f <= 201;
                                assert((j * fuel_cap + (f - cost_val)) as int == j as int * fc + (f as int - cost_val as int)) by (nonlinear_arith)
                                    requires fc == fuel_cap as int, fuel_cap <= 201, j <= 100, f <= 201, f >= cost_val;
                            }
                            dp.set(city * fuel_cap + f, (dp[city * fuel_cap + f] + dp[j * fuel_cap + (f - cost_val)]) % modv);
                            proof {
                                
                                assert forall |i2: int, fp2: int| #![trigger dp@[i2 * fc + fp2]]
                                    0 <= i2 && i2 < n_int && 0 <= fp2 && fp2 < (f as int)
                                    implies {
                                        &&& dp@[i2 * fc + fp2] as int
                                            == Self::dp(locs, n_int, i2, finish_int, fp2, 0) % MOD_INT
                                        &&& 0 <= dp@[i2 * fc + fp2] < modv
                                    }
                                by {
                                    assert(0 <= i2 * fc + fp2 && i2 * fc + fp2 < dp@.len() as int) by (nonlinear_arith)
                                        requires 0 <= i2, i2 < (n as int), 0 <= fp2, fp2 < (fuel_cap as int),
                                            dp@.len() == total_size, total_size == n * fuel_cap, n >= 2, fuel_cap >= 2,
                                            fc == (fuel_cap as int);
                                    if i2 == city as int {
                                        assert(fp2 != (f as int));
                                    } else {
                                        assert(i2 * fc + fp2 != (city as int) * fc + (f as int)) by (nonlinear_arith)
                                            requires i2 != (city as int), 0 <= i2, i2 < (n as int),
                                                0 <= fp2, fp2 < (fuel_cap as int), 0 <= (city as int), (city as int) < (n as int),
                                                0 <= (f as int), (f as int) < (fuel_cap as int),
                                                fc == (fuel_cap as int), fuel_cap >= 2;
                                    }
                                };

                                
                                assert forall |i2: int| #![trigger dp@[i2 * fc + f as int]]
                                    0 <= i2 && i2 < (city as int)
                                    implies {
                                        &&& dp@[i2 * fc + f as int] as int
                                            == Self::dp(locs, n_int, i2, finish_int, f as int, 0) % MOD_INT
                                        &&& 0 <= dp@[i2 * fc + f as int] < modv
                                    }
                                by {
                                    assert(0 <= i2 * fc + (f as int) && i2 * fc + (f as int) < dp@.len() as int) by (nonlinear_arith)
                                        requires 0 <= i2, i2 < (n as int), 0 <= (f as int), (f as int) < (fuel_cap as int),
                                            dp@.len() == total_size, total_size == n * fuel_cap, n >= 2, fuel_cap >= 2,
                                            fc == (fuel_cap as int);
                                    assert(i2 * fc + (f as int) != (city as int) * fc + (f as int)) by (nonlinear_arith)
                                        requires i2 < (city as int), 0 <= i2, i2 < (n as int),
                                            0 <= (city as int), (city as int) < (n as int),
                                            fc == (fuel_cap as int), fuel_cap >= 2;
                                };

                                
                                assert forall |i2: int| #![trigger dp@[i2 * fc + f as int]]
                                    (city as int) < i2 && i2 < n_int
                                    implies dp@[i2 * fc + f as int] == (if i2 == finish_int { 1i64 } else { 0i64 })
                                by {
                                    assert(0 <= i2 * fc + (f as int) && i2 * fc + (f as int) < dp@.len() as int) by (nonlinear_arith)
                                        requires 0 <= i2, i2 < (n as int), 0 <= (f as int), (f as int) < (fuel_cap as int),
                                            dp@.len() == total_size, total_size == n * fuel_cap, n >= 2, fuel_cap >= 2,
                                            fc == (fuel_cap as int);
                                    assert(i2 * fc + (f as int) != (city as int) * fc + (f as int)) by (nonlinear_arith)
                                        requires i2 > (city as int), 0 <= i2, i2 < (n as int),
                                            0 <= (city as int), (city as int) < (n as int),
                                            fc == (fuel_cap as int), fuel_cap >= 2;
                                };

                                
                                assert forall |i2: int, fp2: int| #![trigger dp@[i2 * fc + fp2]]
                                    0 <= i2 && i2 < n_int && (f as int) < fp2 && fp2 < fc
                                    implies dp@[i2 * fc + fp2] == (if i2 == finish_int { 1i64 } else { 0i64 })
                                by {
                                    assert(0 <= i2 * fc + fp2 && i2 * fc + fp2 < dp@.len() as int) by (nonlinear_arith)
                                        requires 0 <= i2, i2 < (n as int), 0 <= fp2, fp2 < (fuel_cap as int),
                                            dp@.len() == total_size, total_size == n * fuel_cap, n >= 2, fuel_cap >= 2,
                                            fc == (fuel_cap as int);
                                    if i2 == city as int {
                                        assert(fp2 > (f as int));
                                        assert(fp2 != (f as int));
                                    } else {
                                        assert(i2 * fc + fp2 != (city as int) * fc + (f as int)) by (nonlinear_arith)
                                            requires i2 != (city as int), 0 <= i2, i2 < (n as int),
                                                0 <= fp2, fp2 < (fuel_cap as int), 0 <= (city as int), (city as int) < (n as int),
                                                0 <= (f as int), (f as int) < (fuel_cap as int),
                                                fc == (fuel_cap as int), fuel_cap >= 2;
                                    }
                                };
                            }
                        }
                    }
                    j = j + 1;
                }

                proof {
                    let h_city = city as int;
                    let h_f = f as int;
                    let bv: int = if h_city == finish_int { 1int } else { 0int };
                    let dp_t = Self::dp(locs, n_int, h_city, finish_int, h_f, 0);
                    assert(Self::dp(locs, n_int, h_city, finish_int, h_f, n_int) == bv);
                    assert(dp_t + bv - bv == dp_t);
                    assert(dp@[h_city * fc + h_f] as int == dp_t % MOD_INT);
                }

                city = city + 1;
            }
            f = f + 1;
        }

        proof {
            let si = start as int;
            let fi_int = fuel as int;
            assert(0 <= si < n_int);
            assert(0 <= fi_int < fc);
            assert(0 <= si * fc + fi_int && si * fc + fi_int < total_size as int) by (nonlinear_arith)
                requires 0 <= si, si < (n as int), 0 <= fi_int, fi_int < (fuel_cap as int),
                    total_size == n * fuel_cap, n >= 2, fuel_cap >= 2,
                    fc == (fuel_cap as int);
            assert(dp@[si * fc + fi_int] as int
                == Self::dp(locs, n_int, si, finish_int, fi_int, 0) % MOD_INT);
            assert(0 <= si * fc + fi_int && si * fc + fi_int < total_size as int) by (nonlinear_arith)
                requires 0 <= si, si < (n as int), 0 <= fi_int, fi_int < (fuel_cap as int),
                    total_size == n * fuel_cap, n >= 2, fuel_cap >= 2,
                    fc == (fuel_cap as int);
        }

        dp[start as usize * fuel_cap + fuel as usize] as i32
    }
}

} 
