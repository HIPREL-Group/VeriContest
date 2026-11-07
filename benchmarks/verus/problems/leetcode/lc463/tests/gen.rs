use vstd::prelude::*;

verus! {

    pub open spec fn adjacent(r1: int, c1: int, r2: int, c2: int) -> bool {
        (r1 == r2 && (c1 + 1 == c2 || c2 + 1 == c1))
            || (c1 == c2 && (r1 + 1 == r2 || r2 + 1 == r1))
    }

    pub open spec fn is_land(grid: Seq<Vec<i32>>, rows: int, cols: int, r: int, c: int) -> bool {
        0 <= r < rows && 0 <= c < cols && grid[r][c] == 1
    }

    pub open spec fn reachable(grid: Seq<Vec<i32>>, rows: int, cols: int, r1: int, c1: int, r2: int, c2: int, fuel: nat) -> bool
        decreases fuel
    {
        if r1 == r2 && c1 == c2 {
            is_land(grid, rows, cols, r1, c1)
        } else if fuel == 0 {
            false
        } else {
            is_land(grid, rows, cols, r1, c1)
            && exists|r3: int, c3: int|
                adjacent(r1, c1, r3, c3)
                && is_land(grid, rows, cols, r3, c3)
                && reachable(grid, rows, cols, r3, c3, r2, c2, (fuel - 1) as nat)
        }
    }

    pub open spec fn exactly_one_island(grid: Seq<Vec<i32>>, rows: int, cols: int) -> bool {
        (exists|r: int, c: int| is_land(grid, rows, cols, r, c))
        && (forall|r1: int, c1: int, r2: int, c2: int|
            is_land(grid, rows, cols, r1, c1) && is_land(grid, rows, cols, r2, c2)
            ==> reachable(grid, rows, cols, r1, c1, r2, c2, (rows * cols) as nat))
    }

    pub open spec fn is_water(grid: Seq<Vec<i32>>, rows: int, cols: int, r: int, c: int) -> bool {
        0 <= r < rows && 0 <= c < cols && grid[r][c] == 0
    }

    pub open spec fn water_reachable(grid: Seq<Vec<i32>>, rows: int, cols: int, r1: int, c1: int, r2: int, c2: int, fuel: nat) -> bool
        decreases fuel
    {
        if r1 == r2 && c1 == c2 {
            is_water(grid, rows, cols, r1, c1)
        } else if fuel == 0 {
            false
        } else {
            is_water(grid, rows, cols, r1, c1)
            && exists|r3: int, c3: int|
                adjacent(r1, c1, r3, c3)
                && is_water(grid, rows, cols, r3, c3)
                && water_reachable(grid, rows, cols, r3, c3, r2, c2, (fuel - 1) as nat)
        }
    }

    pub open spec fn is_border_water(grid: Seq<Vec<i32>>, rows: int, cols: int, r: int, c: int) -> bool {
        is_water(grid, rows, cols, r, c) && (r == 0 || r == rows - 1 || c == 0 || c == cols - 1)
    }

    pub open spec fn no_lakes(grid: Seq<Vec<i32>>, rows: int, cols: int) -> bool {
        forall|r: int, c: int| is_water(grid, rows, cols, r, c) ==>
            exists|br: int, bc: int| is_border_water(grid, rows, cols, br, bc)
                && water_reachable(grid, rows, cols, r, c, br, bc, (rows * cols) as nat)
    }


pub open spec fn band_shape(grid: Seq<Vec<i32>>, rows: int, cols: int, lo: Seq<i32>, hi: Seq<i32>, spine: int) -> bool {
    1 <= rows <= 100 && 1 <= cols <= 100 && grid.len() == rows
    && lo.len() == rows && hi.len() == rows && 0 <= spine < cols
    && (forall|r: int| 0 <= r < rows ==> #[trigger] grid[r].len() == cols)
    && (forall|r: int| 0 <= r < rows ==> 0 <= #[trigger] lo[r] <= spine)
    && (forall|r: int| 0 <= r < rows ==> spine <= #[trigger] hi[r] < cols)
    && (forall|r: int, c: int| 0 <= r < rows && 0 <= c < cols ==>
        #[trigger] grid[r][c] == if lo[r] <= c <= hi[r] { 1i32 } else { 0i32 })
}
pub open spec fn delta(a: int, b: int) -> int { if a >= b { a - b } else { b - a } }
pub open spec fn band_distance(r1: int, c1: int, r2: int, c2: int, spine: int) -> int {
    if r1 == r2 { delta(c1, c2) } else { delta(c1, spine) + delta(r1, r2) + delta(c2, spine) }
}
proof fn band_land_path(grid: Seq<Vec<i32>>, rows: int, cols: int, lo: Seq<i32>, hi: Seq<i32>, spine: int,
    r1: int, c1: int, r2: int, c2: int, fuel: nat)
    requires band_shape(grid, rows, cols, lo, hi, spine),
        is_land(grid, rows, cols, r1, c1), is_land(grid, rows, cols, r2, c2),
        band_distance(r1, c1, r2, c2, spine) <= fuel,
    ensures reachable(grid, rows, cols, r1, c1, r2, c2, fuel),
    decreases fuel,
{
    if r1 != r2 || c1 != c2 {
        assert(fuel > 0);
        let nr = if r1 != r2 && c1 == spine { if r1 < r2 { r1 + 1 } else { r1 - 1 } } else { r1 };
        let nc = if r1 == r2 { if c1 < c2 { c1 + 1 } else { c1 - 1 } }
            else if c1 < spine { c1 + 1 } else if c1 > spine { c1 - 1 } else { c1 };
        assert(lo[nr] <= nc <= hi[nr]);
        assert(is_land(grid, rows, cols, nr, nc));
        assert(band_distance(nr, nc, r2, c2, spine) <= fuel - 1);
        band_land_path(grid, rows, cols, lo, hi, spine, nr, nc, r2, c2, (fuel - 1) as nat);
        assert(adjacent(r1, c1, nr, nc));
        assert(exists|r3: int, c3: int| adjacent(r1, c1, r3, c3)
            && is_land(grid, rows, cols, r3, c3)
            && reachable(grid, rows, cols, r3, c3, r2, c2, (fuel - 1) as nat));
    }
}
proof fn band_water_path(grid: Seq<Vec<i32>>, rows: int, cols: int, lo: Seq<i32>, hi: Seq<i32>, spine: int,
    r: int, c: int, border: int, fuel: nat)
    requires band_shape(grid, rows, cols, lo, hi, spine), is_water(grid, rows, cols, r, c),
        border == (if c < lo[r] { 0int } else { cols - 1 }), delta(c, border) <= fuel,
    ensures is_border_water(grid, rows, cols, r, border),
        water_reachable(grid, rows, cols, r, c, r, border, fuel),
    decreases fuel,
{
    if c != border {
        assert(fuel > 0);
        let nc = if c < lo[r] { c - 1 } else { c + 1 };
        assert(is_water(grid, rows, cols, r, nc));
        band_water_path(grid, rows, cols, lo, hi, spine, r, nc, border, (fuel - 1) as nat);
        assert(adjacent(r, c, r, nc));
        assert(exists|r3: int, c3: int| adjacent(r, c, r3, c3)
            && is_water(grid, rows, cols, r3, c3)
            && water_reachable(grid, rows, cols, r3, c3, r, border, (fuel - 1) as nat));
    }
}
proof fn band_is_valid(grid: Seq<Vec<i32>>, rows: int, cols: int, lo: Seq<i32>, hi: Seq<i32>, spine: int)
    requires band_shape(grid, rows, cols, lo, hi, spine),
    ensures exactly_one_island(grid, rows, cols), no_lakes(grid, rows, cols),
{
    assert(is_land(grid, rows, cols, 0, spine));
    assert forall|r1: int, c1: int, r2: int, c2: int|
        is_land(grid, rows, cols, r1, c1) && is_land(grid, rows, cols, r2, c2)
        implies reachable(grid, rows, cols, r1, c1, r2, c2, (rows * cols) as nat) by {
        if r1 == r2 {
            assert(cols - 1 <= rows * cols) by(nonlinear_arith) requires rows >= 1, cols >= 1;
        } else {
            assert(2 * (cols - 1) + rows - 1 <= rows * cols) by(nonlinear_arith)
                requires rows >= 2, cols >= 1;
        }
        band_land_path(grid, rows, cols, lo, hi, spine, r1, c1, r2, c2, (rows * cols) as nat);
    }
    assert forall|r: int, c: int| is_water(grid, rows, cols, r, c) implies
        exists|br: int, bc: int| is_border_water(grid, rows, cols, br, bc)
            && water_reachable(grid, rows, cols, r, c, br, bc, (rows * cols) as nat) by {
        let border = if c < lo[r] { 0int } else { cols - 1 };
        assert(cols - 1 <= rows * cols) by(nonlinear_arith) requires rows >= 1, cols >= 1;
        band_water_path(grid, rows, cols, lo, hi, spine, r, c, border, (rows * cols) as nat);
    }
}
pub fn generate_test_case(raw: Vec<Vec<i32>>) -> (grid: Vec<Vec<i32>>)
    ensures 1 <= grid.len() <= 100, 1 <= grid[0].len() <= 100,
        forall|i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == grid[0].len(),
        forall|i: int, j: int| 0 <= i < grid.len() && 0 <= j < grid[i].len() ==>
            #[trigger] grid[i][j] == 0 || #[trigger] grid[i][j] == 1,
        exactly_one_island(grid@, grid.len() as int, grid[0].len() as int),
        no_lakes(grid@, grid.len() as int, grid[0].len() as int),
{
    let rows = if raw.len() == 0 { 1usize } else if raw.len() > 100 { 100usize } else { raw.len() };
    let cols = if raw.len() == 0 || raw[0].len() == 0 { 1usize }
        else if raw[0].len() > 100 { 100usize } else { raw[0].len() };
    let mut spine = cols / 2;
    let mut c = 0usize;
    while c < cols
        invariant c <= cols, 1 <= cols <= 100, spine < cols,
        decreases cols - c,
    {
        if raw.len() > 0 && c < raw[0].len() && raw[0][c] == 1 { spine = c; }
        c += 1;
    }
    let mut grid: Vec<Vec<i32>> = Vec::new();
    let mut lows: Vec<i32> = Vec::new();
    let mut highs: Vec<i32> = Vec::new();
    let mut r = 0usize;
    while r < rows
        invariant r <= rows, 1 <= rows <= 100, 1 <= cols <= 100, spine < cols,
            grid.len() == r, lows.len() == r, highs.len() == r,
            forall|j: int| 0 <= j < r ==> #[trigger] grid[j].len() == cols,
            forall|j: int| 0 <= j < r ==> 0 <= #[trigger] lows[j] <= spine,
            forall|j: int| 0 <= j < r ==> spine <= #[trigger] highs[j] < cols,
            forall|j: int, k: int| 0 <= j < r && 0 <= k < cols ==>
                #[trigger] grid[j][k] == if lows[j] <= k <= highs[j] { 1i32 } else { 0i32 },
        decreases rows - r,
    {
        let mut low = spine;
        let mut high = spine;
        let mut c = 0usize;
        while c < cols
            invariant c <= cols, 1 <= cols <= 100, low <= spine <= high < cols,
            decreases cols - c,
        {
            if r < raw.len() && c < raw[r].len() && raw[r][c] == 1 {
                if c < low { low = c; }
                if c > high { high = c; }
            }
            c += 1;
        }
        let mut row: Vec<i32> = Vec::new();
        let mut c = 0usize;
        while c < cols
            invariant c <= cols, 1 <= cols <= 100, row.len() == c, low <= spine <= high < cols,
                forall|j: int| 0 <= j < c ==> #[trigger] row[j] == if low <= j <= high { 1i32 } else { 0i32 },
            decreases cols - c,
        {
            row.push(if low <= c && c <= high { 1 } else { 0 });
            c += 1;
        }
        lows.push(low as i32); highs.push(high as i32); grid.push(row);
        r += 1;
    }
    proof {
        assert(band_shape(grid@, rows as int, cols as int, lows@, highs@, spine as int));
        band_is_valid(grid@, rows as int, cols as int, lows@, highs@, spine as int);
    }
    grid
}


/// Builds a valid `rows × cols` grid of 0/1 values from a flat array,
/// optionally applying a mutation to vary the output.
pub fn generate_candidate(
    rows: usize,
    cols: usize,
    values: Vec<i32>,
    mutation_kind: u8,
) -> (result: Vec<Vec<i32>>)
    requires
        1 <= rows <= 100,
        1 <= cols <= 100,
        values.len() == rows * cols,
        forall|k: int| 0 <= k < values.len() ==> (#[trigger] values[k] == 0 || #[trigger] values[k] == 1),
    ensures
        1 <= result.len() <= 100,
        1 <= result[0].len() <= 100,
        forall |i: int| 0 <= i < result.len() ==> #[trigger] result[i].len() == result[0].len(),
        forall |i: int, j: int|
            0 <= i < result.len() && 0 <= j < result[i].len() ==> #[trigger] result[i][j] == 0 || #[trigger] result[i][j] == 1,
{
    let mut grid: Vec<Vec<i32>> = Vec::new();
    let mut r: usize = 0;
    while r < rows
        invariant
            0 <= r <= rows,
            1 <= rows <= 100,
            1 <= cols <= 100,
            grid.len() == r,
            values.len() == rows * cols,
            forall|k: int| 0 <= k < values.len() ==> (values[k] == 0 || values[k] == 1),
            forall|i: int| 0 <= i < r as int ==> (#[trigger] grid[i].len()) == cols,
            forall|i: int, j: int| 0 <= i < r as int && 0 <= j < cols as int
                ==> (#[trigger] grid[i][j] == 0 || #[trigger] grid[i][j] == 1),
        decreases rows - r,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut c: usize = 0;
        while c < cols
            invariant
                0 <= c <= cols,
                0 <= r < rows,
                1 <= rows <= 100,
                1 <= cols <= 100,
                row.len() == c,
                values.len() == rows * cols,
                mutation_kind == mutation_kind,
                forall|k: int| 0 <= k < values.len() ==> (values[k] == 0 || values[k] == 1),
                forall|j: int| 0 <= j < c as int ==> (#[trigger] row[j] == 0 || #[trigger] row[j] == 1),
            decreases cols - c,
        {
            assert(r * cols + c < rows * cols) by(nonlinear_arith)
                requires r < rows, c < cols, cols >= 1;

            let idx = r * cols + c;
            let base_val = values[idx];

            let val: i32 = if mutation_kind == 1u8 && r == 0 && c == 0 {
                // Flip first cell
                1i32 - base_val
            } else if mutation_kind == 2u8 && r == rows - 1 && c == cols - 1 {
                // Flip last cell
                1i32 - base_val
            } else if mutation_kind == 3u8 {
                // All ones
                1i32
            } else if mutation_kind == 4u8 {
                // All zeros
                0i32
            } else if mutation_kind == 5u8 && r == 0 {
                // First row all ones
                1i32
            } else if mutation_kind == 6u8 && r == rows - 1 {
                // Last row all zeros
                0i32
            } else {
                // Identity / fallback
                base_val
            };
            row.push(val);
            c += 1;
        }
        grid.push(row);
        r += 1;
    }
    grid
}

} // verus!

// ---------------------------------------------------------------------------
// Unverified harness
// ---------------------------------------------------------------------------

extern crate serde_json;
use serde_json::json;

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }

    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }

    fn gen_bool(&mut self, pct: u64) -> bool {
        self.next_u64() % 100 < pct
    }
}

struct Solution;
include!("../code.rs");

fn random_values(rng: &mut Rng, len: usize, density: u64) -> Vec<i32> {
    (0..len).map(|_| if rng.gen_bool(density) { 1 } else { 0 }).collect()
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(463);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut n = 0usize;

    let mut emit = |grid: Vec<Vec<i32>>,
                    seen: &mut HashSet<String>,
                    out: &mut std::io::BufWriter<std::fs::File>,
                    n: &mut usize| {
        let grid = generate_test_case(grid);
        if *n >= count { return; }
        let key = format!("{:?}", grid);
        if !seen.insert(key) { return; }
        let output = Solution::island_perimeter(grid.clone());
        writeln!(out, "{}", json!({"input": {"grid": grid}, "output": output})).unwrap();
        *n += 1;
    };

    // ---- Example inputs from description.md ----
    emit(vec![
        vec![0,1,0,0],
        vec![1,1,1,0],
        vec![0,1,0,0],
        vec![1,1,0,0],
    ], &mut seen, &mut out, &mut n);

    emit(vec![vec![1]], &mut seen, &mut out, &mut n);
    emit(vec![vec![1, 0]], &mut seen, &mut out, &mut n);

    // ---- Boundary grids ----
    // All 1s (1×1)
    emit(generate_candidate(1, 1, vec![1], 0), &mut seen, &mut out, &mut n);
    // All 0s (1×1)
    emit(generate_candidate(1, 1, vec![0], 0), &mut seen, &mut out, &mut n);
    // Single row
    emit(generate_candidate(1, 5, vec![1,0,1,0,1], 0), &mut seen, &mut out, &mut n);
    // Single column
    emit(generate_candidate(5, 1, vec![1,0,1,0,1], 0), &mut seen, &mut out, &mut n);

    let num_mutations: u8 = 7;

    // ---- Size classes × density × mutations ----
    let size_classes: Vec<(usize, usize)> = vec![
        (1, 1), (1, 2), (2, 1), (2, 2), (3, 3),
        (1, 100), (100, 1),
        (5, 5), (10, 10), (10, 1), (1, 10),
        (20, 20), (50, 50), (100, 100),
        (7, 13), (13, 7), (25, 4), (4, 25),
        (99, 99), (100, 50), (50, 100),
    ];
    let densities: Vec<u64> = vec![0, 10, 30, 50, 70, 90, 100];

    for &(rows, cols) in &size_classes {
        for &density in &densities {
            if n >= count { break; }
            let vals = random_values(&mut rng, rows * cols, density);
            let mk = (rng.next_u64() % num_mutations as u64) as u8;
            let grid = generate_candidate(rows, cols, vals, mk);
            emit(grid, &mut seen, &mut out, &mut n);
        }
    }

    // ---- Fill remaining with random sizes, densities, and mutations ----
    while n < count {
        let rows = match n % 5 {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 30),
            3 => rng.gen_range_usize(31, 70),
            _ => rng.gen_range_usize(71, 100),
        };
        let cols = match n % 7 {
            0 => 1,
            1 => rng.gen_range_usize(1, 5),
            2 => rng.gen_range_usize(1, 10),
            3 => rng.gen_range_usize(11, 30),
            4 => rng.gen_range_usize(31, 60),
            5 => rng.gen_range_usize(61, 100),
            _ => 100,
        };
        let density = *[0u64, 10, 25, 50, 75, 90, 100]
            .get(rng.gen_range_usize(0, 6))
            .unwrap();
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let vals = random_values(&mut rng, rows * cols, density);
        let grid = generate_candidate(rows, cols, vals, mk);
        emit(grid, &mut seen, &mut out, &mut n);
    }
}
