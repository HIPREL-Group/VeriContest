use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn spec_i2max(a: int, b: int) -> int {
    if a > b {
        a
    } else {
        b
    }
}

pub open spec fn spec_i4max(a: int, b: int, c: int, d: int) -> int {
    spec_i2max(spec_i2max(a, b), spec_i2max(c, d))
}

pub open spec fn spec_cell(grid: Seq<i64>, n: int, r: int, c: int) -> int
    recommends
        grid.len() == n * n,
        0 <= r < n,
        0 <= c < n,
{
    grid[r * n + c] as int
}

pub open spec fn spec_orbit_max4(grid: Seq<i64>, n: int, i: int, j: int) -> int
    recommends
        n % 2 == 0,
        2 <= n <= 1000,
        grid.len() == n * n,
        0 <= i < n / 2,
        0 <= j < n / 2,
{
    spec_i4max(
        spec_cell(grid, n, i, j),
        spec_cell(grid, n, j, n - 1 - i),
        spec_cell(grid, n, n - 1 - i, n - 1 - j),
        spec_cell(grid, n, n - 1 - j, i),
    )
}

pub open spec fn spec_orbit_cost(grid: Seq<i64>, n: int, i: int, j: int) -> int
    recommends
        n % 2 == 0,
        2 <= n <= 1000,
        grid.len() == n * n,
        0 <= i < n / 2,
        0 <= j < n / 2,
{
    let m = spec_orbit_max4(grid, n, i, j);
    (m - spec_cell(grid, n, i, j)) + (m - spec_cell(grid, n, j, n - 1 - i))
        + (m - spec_cell(grid, n, n - 1 - i, n - 1 - j)) + (m - spec_cell(grid, n, n - 1 - j, i))
}

proof fn lemma_spec_row_sum_unfold(grid: Seq<i64>, n: int, ri: int, j_end: int)
    requires
        n % 2 == 0,
        2 <= n <= 1000,
        grid.len() == n * n,
        0 <= ri < n / 2,
        0 < j_end <= n / 2,
    ensures
        Solution::spec_row_sum(grid, n, ri, j_end)
            == Solution::spec_row_sum(grid, n, ri, j_end - 1) + spec_orbit_cost(grid, n, ri, j_end - 1),
{
}

proof fn lemma_spec_row_sum_zero(grid: Seq<i64>, n: int, ri: int)
    requires
        n % 2 == 0,
        2 <= n <= 1000,
        grid.len() == n * n,
        0 <= ri < n / 2,
    ensures
        Solution::spec_row_sum(grid, n, ri, 0) == 0,
{
}

proof fn lemma_spec_rows_sum_unfold(grid: Seq<i64>, n: int, ri_end: int)
    requires
        n % 2 == 0,
        2 <= n <= 1000,
        grid.len() == n * n,
        0 < ri_end <= n / 2,
    ensures
        Solution::spec_rows_sum(grid, n, ri_end)
            == Solution::spec_rows_sum(grid, n, ri_end - 1)
                + Solution::spec_row_sum(grid, n, ri_end - 1, n / 2),
{
}

proof fn lemma_spec_rows_sum_zero(grid: Seq<i64>, n: int)
    requires
        n % 2 == 0,
        2 <= n <= 1000,
        grid.len() == n * n,
    ensures
        Solution::spec_rows_sum(grid, n, 0) == 0,
{
}

proof fn lemma_spec_cell_bounds(grid: Seq<i64>, n: int, r: int, c: int)
    requires
        grid.len() == n * n,
        0 <= r < n,
        0 <= c < n,
        forall|k: int|
            0 <= k < grid.len() ==> 0 <= (#[trigger] grid[k] as int) && (grid[k] as int) <= 25,
    ensures
        0 <= spec_cell(grid, n, r, c) <= 25,
{
    assert(0 <= r * n + c && r * n + c < n * n) by (nonlinear_arith)
        requires
            0 <= r < n,
            0 <= c < n,
    {
    }
    assert((r * n + c) as int == r * n + c);
    assert(0 <= r * n + c < grid.len());
    let k = r * n + c;
    assert(0 <= k < grid.len());
    assert(0 <= grid[k] as int && grid[k] as int <= 25);
    assert(spec_cell(grid, n, r, c) == grid[k] as int);
}

proof fn lemma_max4_ge_each(a: int, b: int, c: int, d: int)
    ensures
        spec_i4max(a, b, c, d) >= a,
        spec_i4max(a, b, c, d) >= b,
        spec_i4max(a, b, c, d) >= c,
        spec_i4max(a, b, c, d) >= d,
{
    assert(spec_i2max(a, b) >= a && spec_i2max(a, b) >= b);
    assert(spec_i2max(c, d) >= c && spec_i2max(c, d) >= d);
    let t = spec_i2max(a, b);
    let u = spec_i2max(c, d);
    assert(spec_i2max(t, u) >= t && spec_i2max(t, u) >= u);
}

proof fn lemma_orbit_linear_indices(n: int, i: int, j: int)
    requires
        n % 2 == 0,
        2 <= n <= 1000,
        0 <= i < n / 2,
        0 <= j < n / 2,
    ensures
        0 <= i * n + j < n * n,
        0 <= j * n + (n - 1 - i) < n * n,
        0 <= (n - 1 - i) * n + (n - 1 - j) < n * n,
        0 <= (n - 1 - j) * n + i < n * n,
{
    assert(0 <= i * n + j && i * n + j < n * n) by (nonlinear_arith)
        requires
            n % 2 == 0,
            2 <= n <= 1000,
            0 <= i < n / 2,
            0 <= j < n / 2,
    {
    }
    assert(0 <= j * n + (n - 1 - i) && j * n + (n - 1 - i) < n * n) by (nonlinear_arith)
        requires
            n % 2 == 0,
            2 <= n <= 1000,
            0 <= i < n / 2,
            0 <= j < n / 2,
    {
    }
    assert(0 <= (n - 1 - i) * n + (n - 1 - j) && (n - 1 - i) * n + (n - 1 - j) < n * n) by (nonlinear_arith)
        requires
            n % 2 == 0,
            2 <= n <= 1000,
            0 <= i < n / 2,
            0 <= j < n / 2,
    {
    }
    assert(0 <= (n - 1 - j) * n + i && (n - 1 - j) * n + i < n * n) by (nonlinear_arith)
        requires
            n % 2 == 0,
            2 <= n <= 1000,
            0 <= i < n / 2,
            0 <= j < n / 2,
    {
    }
}

proof fn lemma_spec_orbit_cost_le_100(grid: Seq<i64>, n: int, i: int, j: int)
    requires
        n % 2 == 0,
        2 <= n <= 1000,
        grid.len() == n * n,
        0 <= i < n / 2,
        0 <= j < n / 2,
        forall|k: int|
            0 <= k < grid.len() ==> 0 <= (#[trigger] grid[k] as int) && (grid[k] as int) <= 25,
    ensures
        spec_orbit_cost(grid, n, i, j) <= 100,
{
    lemma_orbit_linear_indices(n, i, j);
    assert(0 <= n - 1 - i && n - 1 - i < n) by (nonlinear_arith)
        requires
            n % 2 == 0,
            2 <= n <= 1000,
            0 <= i < n / 2,
    {
    }
    assert(0 <= n - 1 - j && n - 1 - j < n) by (nonlinear_arith)
        requires
            n % 2 == 0,
            2 <= n <= 1000,
            0 <= j < n / 2,
    {
    }
    lemma_spec_cell_bounds(grid, n, i, j);
    lemma_spec_cell_bounds(grid, n, j, n - 1 - i);
    lemma_spec_cell_bounds(grid, n, n - 1 - i, n - 1 - j);
    lemma_spec_cell_bounds(grid, n, n - 1 - j, i);
    let a = spec_cell(grid, n, i, j);
    let b = spec_cell(grid, n, j, n - 1 - i);
    let c = spec_cell(grid, n, n - 1 - i, n - 1 - j);
    let d = spec_cell(grid, n, n - 1 - j, i);
    assert(0 <= a && a <= 25);
    assert(0 <= b && b <= 25);
    assert(0 <= c && c <= 25);
    assert(0 <= d && d <= 25);
    let m = spec_orbit_max4(grid, n, i, j);
    assert(m == spec_i4max(a, b, c, d));
    lemma_max4_ge_each(a, b, c, d);
    assert(m - a <= 25);
    assert(m - b <= 25);
    assert(m - c <= 25);
    assert(m - d <= 25);
    assert(spec_orbit_cost(grid, n, i, j) == (m - a) + (m - b) + (m - c) + (m - d));
}

proof fn lemma_spec_row_sum_le_j100(grid: Seq<i64>, n: int, ri: int, j_end: int)
    requires
        n % 2 == 0,
        2 <= n <= 1000,
        grid.len() == n * n,
        0 <= ri < n / 2,
        0 <= j_end <= n / 2,
        forall|k: int|
            0 <= k < grid.len() ==> 0 <= (#[trigger] grid[k] as int) && (grid[k] as int) <= 25,
    ensures
        Solution::spec_row_sum(grid, n, ri, j_end) <= j_end * 100,
    decreases j_end + 1,
{
    if j_end <= 0 {
        assert(Solution::spec_row_sum(grid, n, ri, j_end) == 0);
    } else {
        lemma_spec_row_sum_le_j100(grid, n, ri, (j_end - 1) as int);
        lemma_spec_orbit_cost_le_100(grid, n, ri, (j_end - 1) as int);
        assert(Solution::spec_row_sum(grid, n, ri, j_end)
            == Solution::spec_row_sum(grid, n, ri, j_end - 1) + spec_orbit_cost(grid, n, ri, j_end - 1));
        assert(Solution::spec_row_sum(grid, n, ri, j_end - 1) <= (j_end - 1) * 100);
        assert(spec_orbit_cost(grid, n, ri, j_end - 1) <= 100);
        assert(Solution::spec_row_sum(grid, n, ri, j_end) <= (j_end - 1) * 100 + 100);
        assert((j_end - 1) * 100 + 100 == j_end * 100) by (nonlinear_arith)
            requires
                0 < j_end <= n / 2,
        {
        }
    }
}

proof fn lemma_spec_rows_sum_le_ri100(grid: Seq<i64>, n: int, ri_end: int)
    requires
        n % 2 == 0,
        2 <= n <= 1000,
        grid.len() == n * n,
        0 <= ri_end <= n / 2,
        forall|k: int|
            0 <= k < grid.len() ==> 0 <= (#[trigger] grid[k] as int) && (grid[k] as int) <= 25,
    ensures
        Solution::spec_rows_sum(grid, n, ri_end) <= ri_end * (n / 2) * 100,
    decreases ri_end + 1,
{
    if ri_end <= 0 {
        assert(ri_end == 0);
        assert(Solution::spec_rows_sum(grid, n, ri_end) == 0);
        assert(ri_end * (n / 2) * 100 == 0 * (n / 2) * 100);
        assert(0 * (n / 2) * 100 == 0);
    } else {
        lemma_spec_rows_sum_le_ri100(grid, n, (ri_end - 1) as int);
        lemma_spec_row_sum_le_j100(grid, n, (ri_end - 1) as int, n / 2);
        assert(Solution::spec_rows_sum(grid, n, ri_end)
            == Solution::spec_rows_sum(grid, n, ri_end - 1)
                + Solution::spec_row_sum(grid, n, ri_end - 1, n / 2));
        assert(Solution::spec_rows_sum(grid, n, ri_end - 1) <= (ri_end - 1) * (n / 2) * 100);
        assert(Solution::spec_row_sum(grid, n, ri_end - 1, n / 2) <= (n / 2) * 100);
        assert(Solution::spec_rows_sum(grid, n, ri_end)
            <= (ri_end - 1) * (n / 2) * 100 + (n / 2) * 100);
        assert((ri_end - 1) * (n / 2) * 100 + (n / 2) * 100 == ri_end * (n / 2) * 100) by (nonlinear_arith)
            requires
                0 < ri_end <= n / 2,
                n % 2 == 0,
                2 <= n <= 1000,
        {
        }
    }
}

proof fn lemma_prefix_sum_le(grid: Seq<i64>, n: int, i: int, j: int)
    requires
        n % 2 == 0,
        2 <= n <= 1000,
        grid.len() == n * n,
        0 <= i < n / 2,
        0 <= j <= n / 2,
        forall|k: int|
            0 <= k < grid.len() ==> 0 <= (#[trigger] grid[k] as int) && (grid[k] as int) <= 25,
    ensures
        Solution::spec_rows_sum(grid, n, i) + Solution::spec_row_sum(grid, n, i, j)
            <= (i * (n / 2) + j) * 100,
{
    lemma_spec_rows_sum_le_ri100(grid, n, i);
    lemma_spec_row_sum_le_j100(grid, n, i, j);
    assert(Solution::spec_rows_sum(grid, n, i) <= i * (n / 2) * 100);
    assert(Solution::spec_row_sum(grid, n, i, j) <= j * 100);
    assert(i * (n / 2) * 100 + j * 100 == (i * (n / 2) + j) * 100) by (nonlinear_arith)
        requires
            0 <= i < n / 2,
            0 <= j <= n / 2,
            n % 2 == 0,
            2 <= n <= 1000,
    {
    }
}

impl Solution {
    pub open spec fn spec_row_sum(grid: Seq<i64>, n: int, ri: int, j_end: int) -> int
        recommends
            n % 2 == 0,
            2 <= n <= 1000,
            grid.len() == n * n,
            0 <= ri < n / 2,
            0 <= j_end <= n / 2,
        decreases j_end + 1,
    {
        if j_end <= 0 {
            0
        } else {
            Self::spec_row_sum(grid, n, ri, j_end - 1) + spec_orbit_cost(grid, n, ri, j_end - 1)
        }
    }

    pub open spec fn spec_rows_sum(grid: Seq<i64>, n: int, ri_end: int) -> int
        recommends
            n % 2 == 0,
            2 <= n <= 1000,
            grid.len() == n * n,
            0 <= ri_end <= n / 2,
        decreases ri_end + 1,
    {
        if ri_end <= 0 {
            0
        } else {
            Self::spec_rows_sum(grid, n, ri_end - 1) + Self::spec_row_sum(grid, n, ri_end - 1, n / 2)
        }
    }

    pub fn min_ops_perfect_square(n: usize, grid: Vec<i64>) -> (res: i64)
        requires
            2 <= (n as int) <= 1000,
            (n as int) % 2 == 0,
            (grid.len() as int) == (n as int) * (n as int),
            forall|k: int|
                0 <= k < (grid.len() as int) ==> 0 <= (#[trigger] grid[k] as int) && (grid[k] as int) <= 25,
        ensures
            (res as int) == Self::spec_rows_sum(grid@, n as int, n as int / 2),
    {
        let half = n / 2;
        proof {
            assert((half as int) == (n as int) / 2);
            lemma_spec_rows_sum_zero(grid@, n as int);
        }
        let mut total: i64 = 0;
        let mut i: usize = 0;
        while i < half
            invariant
                grid.len() == n * n,
                2 <= (n as int) <= 1000,
                (n as int) % 2 == 0,
                (grid@.len() as int) == (n as int) * (n as int),
                forall|k: int|
                    0 <= k < (grid@.len() as int) ==> 0 <= (#[trigger] grid@[k] as int) && (grid@[k] as int) <= 25,
                i <= half,
                (half as int) == (n as int) / 2,
                (i as int) <= (n as int) / 2,
                (total as int) == Self::spec_rows_sum(grid@, n as int, i as int),
                (total as int) >= 0,
            decreases half - i,
        {
            proof {
                lemma_spec_rows_sum_le_ri100(grid@, n as int, i as int);
                lemma_spec_row_sum_zero(grid@, n as int, i as int);
                assert((total as int) == Self::spec_rows_sum(grid@, n as int, i as int));
                assert(Self::spec_row_sum(grid@, n as int, i as int, 0) == 0);
                assert((total as int) <= (i as int) * ((n as int) / 2) * 100);
                assert((i as int) * ((n as int) / 2) * 100 == (i as int) * (half as int) * 100);
                assert((i as int) * (half as int) * 100 == ((i as int) * (half as int) + 0) * 100);
            }
            let mut j: usize = 0;
            while j < half
                invariant
                    grid.len() == n * n,
                    2 <= (n as int) <= 1000,
                    (n as int) % 2 == 0,
                    (grid@.len() as int) == (n as int) * (n as int),
                    forall|k: int|
                        0 <= k < (grid@.len() as int) ==> 0 <= (#[trigger] grid@[k] as int) && (grid@[k] as int) <= 25,
                    i < half,
                    (i as int) < (n as int) / 2,
                    j <= half,
                    (half as int) == (n as int) / 2,
                    (total as int) == Self::spec_rows_sum(grid@, n as int, i as int)
                        + Self::spec_row_sum(grid@, n as int, i as int, j as int),
                    (total as int)
                        <= ((i as int) * (half as int) + (j as int)) * 100,
                    (total as int) >= 0,
                decreases half - j,
            {
                proof {
                    lemma_orbit_linear_indices(n as int, i as int, j as int);
                    assert(((i * n + j) as int) < (grid.len() as int));
                    assert(((j * n + (n - 1 - i)) as int) < (grid.len() as int));
                    assert((((n - 1 - i) * n + (n - 1 - j)) as int) < (grid.len() as int));
                    assert((((n - 1 - j) * n + i) as int) < (grid.len() as int));
                    assert((i * n + j) < grid.len());
                    assert((j * n + (n - 1 - i)) < grid.len());
                    assert(((n - 1 - i) * n + (n - 1 - j)) < grid.len());
                    assert(((n - 1 - j) * n + i) < grid.len());
                }
                let v0 = grid[i * n + j];
                let v1 = grid[j * n + (n - 1 - i)];
                let v2 = grid[(n - 1 - i) * n + (n - 1 - j)];
                let v3 = grid[(n - 1 - j) * n + i];
                proof {
                    assert(0 <= v0 as int && (v0 as int) <= 25);
                    assert(0 <= v1 as int && (v1 as int) <= 25);
                    assert(0 <= v2 as int && (v2 as int) <= 25);
                    assert(0 <= v3 as int && (v3 as int) <= 25);
                }
                let mut m = v0;
                if v1 > m {
                    m = v1;
                }
                if v2 > m {
                    m = v2;
                }
                if v3 > m {
                    m = v3;
                }
                proof {
                    assert((m as int) == spec_i4max(v0 as int, v1 as int, v2 as int, v3 as int));
                    lemma_max4_ge_each(v0 as int, v1 as int, v2 as int, v3 as int);
                    assert((m as int) >= (v0 as int) && (m as int) >= (v1 as int)
                        && (m as int) >= (v2 as int) && (m as int) >= (v3 as int));
                    assert(spec_cell(grid@, n as int, i as int, j as int) == v0 as int);
                    assert(spec_cell(grid@, n as int, j as int, (n as int) - 1 - i as int) == v1 as int);
                    assert(spec_cell(grid@, n as int, (n as int) - 1 - i as int, (n as int) - 1 - j as int) == v2 as int);
                    assert(spec_cell(grid@, n as int, (n as int) - 1 - j as int, i as int) == v3 as int);
                    assert((m as int) == spec_orbit_max4(grid@, n as int, i as int, j as int));
                    lemma_spec_row_sum_unfold(grid@, n as int, i as int, (j + 1) as int);
                    let step = (m - v0) + (m - v1) + (m - v2) + (m - v3);
                    assert((step as int) == spec_orbit_cost(grid@, n as int, i as int, j as int));
                    assert((step as int) >= 0);
                    assert((step as int) <= 100);
                    assert((total as int) + (step as int) == Self::spec_rows_sum(grid@, n as int, i as int)
                        + Self::spec_row_sum(grid@, n as int, i as int, (j + 1) as int));
                    lemma_prefix_sum_le(grid@, n as int, i as int, j as int);
                    assert((total as int) <= ((i as int) * (half as int) + (j as int)) * 100);
                    assert((step as int) <= 100);
                    assert((total as int) + (step as int)
                        <= ((i as int) * (half as int) + (j as int) + 1) * 100);
                    assert(((i as int) * (half as int) + (j as int) + 1) * 100 <= 25_000_000) by (nonlinear_arith)
                        requires
                            2 <= (n as int) <= 1000,
                            (i as int) < (n as int) / 2,
                            (j as int) < (n as int) / 2,
                            (half as int) == (n as int) / 2,
                    {
                    }
                    assert((total as int) + (step as int) < 0x7fff_ffff_ffff_ffff) by (nonlinear_arith)
                        requires
                            (total as int) + (step as int) <= 25_000_000,
                    {
                    }
                }
                total = total + (m - v0) + (m - v1) + (m - v2) + (m - v3);
                j = j + 1;
            }
            proof {
                assert(j == half);
                assert((j as int) == (n as int) / 2);
                assert(Self::spec_row_sum(grid@, n as int, i as int, (n as int) / 2)
                    == Self::spec_row_sum(grid@, n as int, i as int, j as int));
                assert((total as int) == Self::spec_rows_sum(grid@, n as int, i as int)
                    + Self::spec_row_sum(grid@, n as int, i as int, j as int));
                lemma_spec_rows_sum_unfold(grid@, n as int, (i + 1) as int);
                assert((total as int) == Self::spec_rows_sum(grid@, n as int, (i + 1) as int));
            }
            i = i + 1;
        }
        proof {
            assert(i == half);
            assert((i as int) == (n as int) / 2);
            assert((total as int) == Self::spec_rows_sum(grid@, n as int, (n as int) / 2));
            lemma_spec_rows_sum_le_ri100(grid@, n as int, (n as int) / 2);
            assert((total as int) <= ((n as int) / 2) * ((n as int) / 2) * 100);
            assert((total as int) <= 25_000_000) by (nonlinear_arith)
                requires
                    2 <= (n as int) <= 1000,
                    (total as int) <= ((n as int) / 2) * ((n as int) / 2) * 100,
            {
            }
        }
        total
    }
}

}
