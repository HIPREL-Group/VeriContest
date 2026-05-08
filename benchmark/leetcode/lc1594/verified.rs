use vstd::prelude::*;
use vstd::arithmetic::power::{pow, lemma_pow0, lemma_pow1, lemma_pow_adds, lemma_pow_positive};

fn main() {}

verus! {

pub struct Solution;














impl Solution {
    pub open spec fn max2(a: int, b: int) -> int {
        if a >= b { a } else { b }
    }

    pub open spec fn min2(a: int, b: int) -> int {
        if a <= b { a } else { b }
    }

    pub open spec fn max4(a: int, b: int, c: int, d: int) -> int {
        Self::max2(Self::max2(a, b), Self::max2(c, d))
    }

    pub open spec fn min4(a: int, b: int, c: int, d: int) -> int {
        Self::min2(Self::min2(a, b), Self::min2(c, d))
    }

    
    
    pub open spec fn max_prod(grid: Seq<Vec<i32>>, i: int, j: int) -> int
        recommends
            0 <= i < grid.len(),
            0 <= j < grid[i].len(),
        decreases i + j when i >= 0 && j >= 0
    {
        if i + j <= 0 {
            grid[0][0] as int
        } else if i <= 0 {
            Self::max_prod(grid, 0, j - 1) * (grid[0][j] as int)
        } else if j <= 0 {
            Self::max_prod(grid, i - 1, 0) * (grid[i][0] as int)
        } else {
            let v = grid[i][j] as int;
            Self::max4(
                Self::max_prod(grid, i - 1, j) * v,
                Self::min_prod(grid, i - 1, j) * v,
                Self::max_prod(grid, i, j - 1) * v,
                Self::min_prod(grid, i, j - 1) * v,
            )
        }
    }

    
    
    pub open spec fn min_prod(grid: Seq<Vec<i32>>, i: int, j: int) -> int
        recommends
            0 <= i < grid.len(),
            0 <= j < grid[i].len(),
        decreases i + j when i >= 0 && j >= 0
    {
        if i + j <= 0 {
            grid[0][0] as int
        } else if i <= 0 {
            Self::min_prod(grid, 0, j - 1) * (grid[0][j] as int)
        } else if j <= 0 {
            Self::min_prod(grid, i - 1, 0) * (grid[i][0] as int)
        } else {
            let v = grid[i][j] as int;
            Self::min4(
                Self::max_prod(grid, i - 1, j) * v,
                Self::min_prod(grid, i - 1, j) * v,
                Self::max_prod(grid, i, j - 1) * v,
                Self::min_prod(grid, i, j - 1) * v,
            )
        }
    }

    proof fn lemma_pow4_unfold(k: nat)
        requires k > 0
        ensures pow(4int, k) == 4 * pow(4int, (k - 1) as nat)
        decreases k
    {
        lemma_pow_adds(4int, 1nat, (k - 1) as nat);
        lemma_pow1(4int);
    }

    proof fn lemma_pow4_positive(k: nat)
        ensures pow(4int, k) >= 1
        decreases k
    {
        lemma_pow_positive(4int, k);
    }

    proof fn lemma_pow4_monotone(a: nat, b: nat)
        requires a <= b
        ensures pow(4int, a) <= pow(4int, b)
        decreases b - a
    {
        if a < b {
            Self::lemma_pow4_monotone(a, (b - 1) as nat);
            Self::lemma_pow4_unfold(b);
            Self::lemma_pow4_positive((b - 1) as nat);
            assert(pow(4int, b) == 4 * pow(4int, (b - 1) as nat));
            assert(pow(4int, (b - 1) as nat) >= 1);
            assert(pow(4int, b) >= pow(4int, (b - 1) as nat));
        }
    }

    proof fn lemma_prod_bounds(grid: Seq<Vec<i32>>, i: int, j: int)
        requires
            grid.len() >= 1,
            grid[0].len() >= 1,
            forall |ii: int| 0 <= ii < grid.len() ==> #[trigger] grid[ii].len() == grid[0].len(),
            forall |ii: int, jj: int|
                0 <= ii < grid.len() && 0 <= jj < grid[ii].len()
                    ==> -4 <= #[trigger] grid[ii][jj] <= 4,
            0 <= i && i < grid.len(),
            0 <= j && j < grid[i].len(),
        ensures
            -pow(4int, (i + j + 1) as nat) <= Self::max_prod(grid, i, j) <= pow(4int, (i + j + 1) as nat),
            -pow(4int, (i + j + 1) as nat) <= Self::min_prod(grid, i, j) <= pow(4int, (i + j + 1) as nat),
        decreases i + j
    {
        if i + j <= 0 {
            lemma_pow1(4int);
            assert(-4 <= grid[0][0] <= 4);
        } else if i <= 0 {
            Self::lemma_prod_bounds(grid, 0, j - 1);
            Self::lemma_pow4_unfold((j + 1) as nat);
            let prev_mx = Self::max_prod(grid, 0, j - 1);
            let prev_mn = Self::min_prod(grid, 0, j - 1);
            let v = grid[0][j] as int;
            assert(-4 <= v <= 4);
            assert(pow(4int, (j + 1) as nat) == 4 * pow(4int, j as nat));
            assert(-pow(4int, (j + 1) as nat) <= prev_mx * v <= pow(4int, (j + 1) as nat)) by (nonlinear_arith)
                requires
                    -pow(4int, j as nat) <= prev_mx <= pow(4int, j as nat),
                    -4 <= v <= 4,
                    pow(4int, (j + 1) as nat) == 4 * pow(4int, j as nat),
            {}
            assert(-pow(4int, (j + 1) as nat) <= prev_mn * v <= pow(4int, (j + 1) as nat)) by (nonlinear_arith)
                requires
                    -pow(4int, j as nat) <= prev_mn <= pow(4int, j as nat),
                    -4 <= v <= 4,
                    pow(4int, (j + 1) as nat) == 4 * pow(4int, j as nat),
            {}
        } else if j <= 0 {
            Self::lemma_prod_bounds(grid, i - 1, 0);
            Self::lemma_pow4_unfold((i + 1) as nat);
            let prev_mx = Self::max_prod(grid, i - 1, 0);
            let prev_mn = Self::min_prod(grid, i - 1, 0);
            let v = grid[i][0] as int;
            assert(-4 <= v <= 4);
            assert(pow(4int, (i + 1) as nat) == 4 * pow(4int, i as nat));
            assert(-pow(4int, (i + 1) as nat) <= prev_mx * v <= pow(4int, (i + 1) as nat)) by (nonlinear_arith)
                requires
                    -pow(4int, i as nat) <= prev_mx <= pow(4int, i as nat),
                    -4 <= v <= 4,
                    pow(4int, (i + 1) as nat) == 4 * pow(4int, i as nat),
            {}
            assert(-pow(4int, (i + 1) as nat) <= prev_mn * v <= pow(4int, (i + 1) as nat)) by (nonlinear_arith)
                requires
                    -pow(4int, i as nat) <= prev_mn <= pow(4int, i as nat),
                    -4 <= v <= 4,
                    pow(4int, (i + 1) as nat) == 4 * pow(4int, i as nat),
            {}
        } else {
            Self::lemma_prod_bounds(grid, i - 1, j);
            Self::lemma_prod_bounds(grid, i, j - 1);
            Self::lemma_pow4_unfold((i + j + 1) as nat);
            let bound_above = pow(4int, (i + j) as nat);
            let bound_left = pow(4int, (i + j) as nat);
            let bound = pow(4int, (i + j + 1) as nat);
            let v = grid[i][j] as int;
            let mx_above = Self::max_prod(grid, i - 1, j);
            let mn_above = Self::min_prod(grid, i - 1, j);
            let mx_left = Self::max_prod(grid, i, j - 1);
            let mn_left = Self::min_prod(grid, i, j - 1);
            Self::lemma_pow4_monotone((i + j) as nat, (i + j) as nat);
            assert(-bound_above <= mx_above <= bound_above);
            assert(-bound_above <= mn_above <= bound_above);
            assert(-bound_left <= mx_left <= bound_left);
            assert(-bound_left <= mn_left <= bound_left);
            assert(-4 <= v <= 4);
            assert(bound == 4 * pow(4int, (i + j) as nat));
            assert(-bound <= mx_above * v <= bound) by (nonlinear_arith)
                requires
                    -bound_above <= mx_above <= bound_above,
                    -4 <= v <= 4,
                    bound == 4 * bound_above,
            {}
            assert(-bound <= mn_above * v <= bound) by (nonlinear_arith)
                requires
                    -bound_above <= mn_above <= bound_above,
                    -4 <= v <= 4,
                    bound == 4 * bound_above,
            {}
            assert(-bound <= mx_left * v <= bound) by (nonlinear_arith)
                requires
                    -bound_left <= mx_left <= bound_left,
                    -4 <= v <= 4,
                    bound == 4 * bound_left,
            {}
            assert(-bound <= mn_left * v <= bound) by (nonlinear_arith)
                requires
                    -bound_left <= mn_left <= bound_left,
                    -4 <= v <= 4,
                    bound == 4 * bound_left,
            {}
        }
    }

    proof fn lemma_pow4_29_fits_i64()
        ensures pow(4int, 29nat) <= i64::MAX as int
    {
        lemma_pow1(4int);
        assert(pow(4int, 1nat) == 4);
        lemma_pow_adds(4int, 1nat, 1nat);
        assert(pow(4int, 2nat) == 16);
        lemma_pow_adds(4int, 2nat, 2nat);
        assert(pow(4int, 4nat) == 256);
        lemma_pow_adds(4int, 4nat, 4nat);
        assert(pow(4int, 8nat) == 65536);
        lemma_pow_adds(4int, 8nat, 8nat);
        assert(pow(4int, 16nat) == 4294967296);
        lemma_pow_adds(4int, 4nat, 1nat);
        assert(pow(4int, 5nat) == 1024);
        lemma_pow_adds(4int, 8nat, 5nat);
        assert(pow(4int, 13nat) == 67108864);
        lemma_pow_adds(4int, 16nat, 13nat);
        assert(pow(4int, 29nat) == 288230376151711744) by (nonlinear_arith)
            requires
                pow(4int, 29nat) == pow(4int, 16nat) * pow(4int, 13nat),
                pow(4int, 16nat) == 4294967296,
                pow(4int, 13nat) == 67108864,
        {}
    }

    proof fn lemma_i64_safe_mul(a: int, b: int, bound: int)
        requires
            -bound <= a <= bound,
            -4 <= b <= 4,
            bound >= 0,
            4 * bound <= i64::MAX as int,
        ensures
            i64::MIN as int <= a * b <= i64::MAX as int,
    {
        assert(i64::MIN as int <= a * b <= i64::MAX as int) by (nonlinear_arith)
            requires
                -bound <= a <= bound,
                -4 <= b <= 4,
                bound >= 0,
                4 * bound <= i64::MAX as int,
        {}
    }

    fn max2_i64(a: i64, b: i64) -> (res: i64)
        ensures
            res as int == Self::max2(a as int, b as int),
    {
        if a >= b { a } else { b }
    }

    fn min2_i64(a: i64, b: i64) -> (res: i64)
        ensures
            res as int == Self::min2(a as int, b as int),
    {
        if a <= b { a } else { b }
    }

    fn max4_i64(a: i64, b: i64, c: i64, d: i64) -> (res: i64)
        ensures
            res as int == Self::max4(a as int, b as int, c as int, d as int),
    {
        Self::max2_i64(Self::max2_i64(a, b), Self::max2_i64(c, d))
    }

    fn min4_i64(a: i64, b: i64, c: i64, d: i64) -> (res: i64)
        ensures
            res as int == Self::min4(a as int, b as int, c as int, d as int),
    {
        Self::min2_i64(Self::min2_i64(a, b), Self::min2_i64(c, d))
    }

    pub fn max_product_path(grid: Vec<Vec<i32>>) -> (result: i32)
        requires
            1 <= grid.len() <= 15,
            1 <= grid[0].len() <= 15,
            forall |i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == grid[0].len(),
            forall |i: int, j: int|
                0 <= i < grid.len() && 0 <= j < grid[i].len()
                    ==> -4 <= #[trigger] grid[i][j] <= 4,
        ensures
            Self::max_prod(grid@, grid@.len() as int - 1, grid[0].len() as int - 1) < 0
                ==> result == -1i32,
            Self::max_prod(grid@, grid@.len() as int - 1, grid[0].len() as int - 1) >= 0
                ==> result == (Self::max_prod(grid@, grid@.len() as int - 1, grid[0].len() as int - 1) % 1_000_000_007) as i32,
    {
        let m = grid.len();
        let n = grid[0].len();
        let ghost g = grid@;

        let mut dp_max: Vec<i64> = Vec::new();
        let mut dp_min: Vec<i64> = Vec::new();

        dp_max.push(grid[0][0] as i64);
        dp_min.push(grid[0][0] as i64);

        proof {
            assert(dp_max@[0] as int == g[0][0] as int);
            assert(dp_min@[0] as int == g[0][0] as int);
            assert(dp_max@[0] as int == Self::max_prod(g, 0, 0));
            assert(dp_min@[0] as int == Self::min_prod(g, 0, 0));
            lemma_pow1(4int);
            assert(-4 <= g[0][0] <= 4);
            assert(-pow(4int, 1nat) <= dp_max@[0] as int <= pow(4int, 1nat));
            assert(-pow(4int, 1nat) <= dp_min@[0] as int <= pow(4int, 1nat));
        }

        let mut j = 1usize;
        while j < n
            invariant
                g == grid@,
                1 <= m <= 15,
                1 <= n <= 15,
                m == grid.len(),
                n == grid[0].len(),
                forall |ii: int| 0 <= ii < grid.len() ==> #[trigger] grid[ii].len() == n,
                forall |ii: int, jj: int|
                    0 <= ii < grid.len() && 0 <= jj < grid[ii].len()
                        ==> -4 <= #[trigger] grid[ii][jj] <= 4,
                1 <= j <= n,
                dp_max.len() == j,
                dp_min.len() == j,
                forall |k: int| 0 <= k < j as int ==> dp_max@[k] as int == Self::max_prod(g, 0, k),
                forall |k: int| 0 <= k < j as int ==> dp_min@[k] as int == Self::min_prod(g, 0, k),
                forall |k: int| 0 <= k < j as int ==>
                    -pow(4int, (k + 1) as nat) <= #[trigger] dp_max@[k] as int <= pow(4int, (k + 1) as nat),
                forall |k: int| 0 <= k < j as int ==>
                    -pow(4int, (k + 1) as nat) <= #[trigger] dp_min@[k] as int <= pow(4int, (k + 1) as nat),
            decreases n - j
        {
            proof {
                Self::lemma_prod_bounds(g, 0, j as int - 1);
                Self::lemma_pow4_unfold((j + 1) as nat);
                Self::lemma_pow4_monotone((j + 1) as nat, 29nat);
                Self::lemma_pow4_29_fits_i64();
                let prev_mx_val = dp_max@[j as int - 1] as int;
                let prev_mn_val = dp_min@[j as int - 1] as int;
                let bound_prev = pow(4int, j as nat);
                Self::lemma_pow4_monotone(j as nat, 28nat);
                assert(-pow(4int, j as nat) <= prev_mx_val <= pow(4int, j as nat));
                assert(-pow(4int, j as nat) <= prev_mn_val <= pow(4int, j as nat));
                assert(pow(4int, 28nat) <= pow(4int, 29nat) / 4) by {
                    Self::lemma_pow4_unfold(29nat);
                }
            }
            let val = grid[0][j] as i64;
            proof {
                Self::lemma_i64_safe_mul(dp_max@[j as int - 1] as int, grid@[0int][j as int] as int, pow(4int, j as nat));
                Self::lemma_i64_safe_mul(dp_min@[j as int - 1] as int, grid@[0int][j as int] as int, pow(4int, j as nat));
            }
            dp_max.push(dp_max[j - 1] * val);
            dp_min.push(dp_min[j - 1] * val);
            proof {
                assert(dp_max@[j as int] as int == Self::max_prod(g, 0, j as int));
                assert(dp_min@[j as int] as int == Self::min_prod(g, 0, j as int));
                Self::lemma_prod_bounds(g, 0, j as int);
                assert forall |k: int| 0 <= k < j as int + 1 implies dp_max@[k] as int == Self::max_prod(g, 0, k) by {
                    if k < j as int {
                    } else {
                        assert(k == j as int);
                    }
                };
                assert forall |k: int| 0 <= k < j as int + 1 implies dp_min@[k] as int == Self::min_prod(g, 0, k) by {
                    if k < j as int {
                    } else {
                        assert(k == j as int);
                    }
                };
            }
            j += 1;
        }

        let mut i = 1usize;
        while i < m
            invariant
                g == grid@,
                1 <= m <= 15,
                1 <= n <= 15,
                m == grid.len(),
                n == grid[0].len(),
                forall |ii: int| 0 <= ii < grid.len() ==> #[trigger] grid[ii].len() == n,
                forall |ii: int, jj: int|
                    0 <= ii < grid.len() && 0 <= jj < grid[ii].len()
                        ==> -4 <= #[trigger] grid[ii][jj] <= 4,
                1 <= i <= m,
                dp_max.len() == n,
                dp_min.len() == n,
                forall |k: int| 0 <= k < n as int ==> dp_max@[k] as int == Self::max_prod(g, i as int - 1, k),
                forall |k: int| 0 <= k < n as int ==> dp_min@[k] as int == Self::min_prod(g, i as int - 1, k),
                forall |k: int| 0 <= k < n as int ==>
                    -pow(4int, (i as int + k) as nat) <= #[trigger] dp_max@[k] as int <= pow(4int, (i as int + k) as nat),
                forall |k: int| 0 <= k < n as int ==>
                    -pow(4int, (i as int + k) as nat) <= #[trigger] dp_min@[k] as int <= pow(4int, (i as int + k) as nat),
            decreases m - i
        {
            proof {
                assert(grid@[i as int].len() == n);
            }
            let v0 = grid[i][0] as i64;
            let old_mx = dp_max[0];
            let old_mn = dp_min[0];
            proof {
                Self::lemma_pow4_monotone((i as int) as nat, 28nat);
                Self::lemma_pow4_29_fits_i64();
                Self::lemma_pow4_unfold(29nat);
                Self::lemma_i64_safe_mul(old_mx as int, grid@[i as int][0int] as int, pow(4int, i as nat));
                Self::lemma_i64_safe_mul(old_mn as int, grid@[i as int][0int] as int, pow(4int, i as nat));
            }
            let ghost old_dp_max = dp_max@;
            let ghost old_dp_min = dp_min@;
            dp_max.set(0, old_mx * v0);
            dp_min.set(0, old_mn * v0);
            proof {
                assert(dp_max@[0] as int == old_mx as int * v0 as int);
                assert(dp_min@[0] as int == old_mn as int * v0 as int);
                assert(dp_max@[0] as int == Self::max_prod(g, i as int, 0));
                assert(dp_min@[0] as int == Self::min_prod(g, i as int, 0));
                Self::lemma_prod_bounds(g, i as int, 0);
            }

            let mut j = 1usize;
            while j < n
                invariant
                    g == grid@,
                    1 <= m <= 15,
                    1 <= n <= 15,
                    m == grid.len(),
                    n == grid[0].len(),
                    forall |ii: int| 0 <= ii < grid.len() ==> #[trigger] grid[ii].len() == n,
                    forall |ii: int, jj: int|
                        0 <= ii < grid.len() && 0 <= jj < grid[ii].len()
                            ==> -4 <= #[trigger] grid[ii][jj] <= 4,
                    1 <= i < m,
                    1 <= j <= n,
                    dp_max.len() == n,
                    dp_min.len() == n,
                    forall |k: int| 0 <= k < j as int ==>
                        dp_max@[k] as int == Self::max_prod(g, i as int, k),
                    forall |k: int| 0 <= k < j as int ==>
                        dp_min@[k] as int == Self::min_prod(g, i as int, k),
                    forall |k: int| j as int <= k < n as int ==>
                        dp_max@[k] as int == Self::max_prod(g, i as int - 1, k),
                    forall |k: int| j as int <= k < n as int ==>
                        dp_min@[k] as int == Self::min_prod(g, i as int - 1, k),
                    forall |k: int| 0 <= k < j as int ==>
                        -pow(4int, (i as int + k + 1) as nat) <= #[trigger] dp_max@[k] as int <= pow(4int, (i as int + k + 1) as nat),
                    forall |k: int| 0 <= k < j as int ==>
                        -pow(4int, (i as int + k + 1) as nat) <= #[trigger] dp_min@[k] as int <= pow(4int, (i as int + k + 1) as nat),
                    forall |k: int| j as int <= k < n as int ==>
                        -pow(4int, (i as int + k) as nat) <= #[trigger] dp_max@[k] as int <= pow(4int, (i as int + k) as nat),
                    forall |k: int| j as int <= k < n as int ==>
                        -pow(4int, (i as int + k) as nat) <= #[trigger] dp_min@[k] as int <= pow(4int, (i as int + k) as nat),
                decreases n - j
            {
                let above_mx = dp_max[j];
                let above_mn = dp_min[j];
                let left_mx = dp_max[j - 1];
                let left_mn = dp_min[j - 1];
                proof {
                    assert(grid@[i as int].len() == n);
                }
                let v = grid[i][j] as i64;
                proof {
                    let ji = j as int;
                    let ii = i as int;
                    assert(above_mx as int == Self::max_prod(g, ii - 1, ji));
                    assert(above_mn as int == Self::min_prod(g, ii - 1, ji));
                    assert(left_mx as int == Self::max_prod(g, ii, ji - 1));
                    assert(left_mn as int == Self::min_prod(g, ii, ji - 1));
                    let bound_above = pow(4int, (ii + ji) as nat);
                    let bound_left = pow(4int, (ii + ji) as nat);
                    Self::lemma_pow4_monotone((ii + ji) as nat, 28nat);
                    Self::lemma_pow4_29_fits_i64();
                    Self::lemma_pow4_unfold(29nat);
                    Self::lemma_i64_safe_mul(above_mx as int, v as int, bound_above);
                    Self::lemma_i64_safe_mul(above_mn as int, v as int, bound_above);
                    Self::lemma_i64_safe_mul(left_mx as int, v as int, bound_left);
                    Self::lemma_i64_safe_mul(left_mn as int, v as int, bound_left);
                }
                let a = above_mx * v;
                let b = above_mn * v;
                let c = left_mx * v;
                let d = left_mn * v;
                let new_mx = Self::max4_i64(a, b, c, d);
                let new_mn = Self::min4_i64(a, b, c, d);
                let ghost old_dp_max_j = dp_max@;
                let ghost old_dp_min_j = dp_min@;
                dp_max.set(j, new_mx);
                dp_min.set(j, new_mn);
                proof {
                    let ji = j as int;
                    let ii = i as int;
                    assert(dp_max@[ji] as int == Self::max_prod(g, ii, ji));
                    assert(dp_min@[ji] as int == Self::min_prod(g, ii, ji));
                    Self::lemma_prod_bounds(g, ii, ji);
                    assert forall |k: int| 0 <= k < ji + 1 implies dp_max@[k] as int == Self::max_prod(g, ii, k) by {
                        if k < ji {
                            assert(dp_max@[k] == old_dp_max_j[k]);
                        }
                    };
                    assert forall |k: int| 0 <= k < ji + 1 implies dp_min@[k] as int == Self::min_prod(g, ii, k) by {
                        if k < ji {
                            assert(dp_min@[k] == old_dp_min_j[k]);
                        }
                    };
                    assert forall |k: int| ji + 1 <= k < n as int implies dp_max@[k] as int == Self::max_prod(g, ii - 1, k) by {
                        assert(dp_max@[k] == old_dp_max_j[k]);
                    };
                    assert forall |k: int| ji + 1 <= k < n as int implies dp_min@[k] as int == Self::min_prod(g, ii - 1, k) by {
                        assert(dp_min@[k] == old_dp_min_j[k]);
                    };
                    assert forall |k: int| 0 <= k < ji + 1 implies
                        -pow(4int, (ii + k + 1) as nat) <= #[trigger] dp_max@[k] as int <= pow(4int, (ii + k + 1) as nat) by {
                        if k < ji {
                            assert(dp_max@[k] == old_dp_max_j[k]);
                        }
                    };
                    assert forall |k: int| 0 <= k < ji + 1 implies
                        -pow(4int, (ii + k + 1) as nat) <= #[trigger] dp_min@[k] as int <= pow(4int, (ii + k + 1) as nat) by {
                        if k < ji {
                            assert(dp_min@[k] == old_dp_min_j[k]);
                        }
                    };
                    assert forall |k: int| ji + 1 <= k < n as int implies
                        -pow(4int, (ii + k) as nat) <= #[trigger] dp_max@[k] as int <= pow(4int, (ii + k) as nat) by {
                        assert(dp_max@[k] == old_dp_max_j[k]);
                    };
                    assert forall |k: int| ji + 1 <= k < n as int implies
                        -pow(4int, (ii + k) as nat) <= #[trigger] dp_min@[k] as int <= pow(4int, (ii + k) as nat) by {
                        assert(dp_min@[k] == old_dp_min_j[k]);
                    };
                }
                j += 1;
            }

            i += 1;
        }

        proof {
            let mi = m as int - 1;
            let ni = n as int - 1;
            assert(dp_max@[ni] as int == Self::max_prod(g, mi, ni));
            Self::lemma_prod_bounds(g, mi, ni);
            Self::lemma_pow4_monotone((mi + ni + 1) as nat, 29nat);
            Self::lemma_pow4_29_fits_i64();
        }
        if dp_max[n - 1] < 0 {
            -1i32
        } else {
            (dp_max[n - 1] % 1_000_000_007i64) as i32
        }
    }
}

}
