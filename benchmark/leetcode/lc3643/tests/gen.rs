use vstd::prelude::*;

verus! {

// Spec fn helpers from spec.rs
pub open spec fn in_square(r: int, c: int, x: int, y: int, k: int) -> bool {
    x <= r < x + k && y <= c < y + k
}

pub open spec fn flipped_row(r: int, x: int, k: int) -> int {
    x + k - 1 - (r - x)
}

pub fn generate_test_case(
    grid: Vec<Vec<i32>>,
    x: i32,
    y: i32,
    k: i32,
    mutation_kind: u8,
) -> (result: (Vec<Vec<i32>>, i32, i32, i32))
    requires
        1 <= grid.len() <= 50,
        1 <= grid[0].len() <= 50,
        forall|r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
        forall|r: int, c: int| 0 <= r < grid.len() && 0 <= c < grid[r].len() ==> 1 <= #[trigger] grid[r][c] <= 100,
        0 <= (x as int),
        (x as int) < grid.len(),
        0 <= (y as int),
        (y as int) < grid[0].len(),
        1 <= (k as int),
        (k as int) <= grid.len() - (x as int),
        (k as int) <= grid[0].len() - (y as int),
    ensures
        1 <= result.0.len() <= 50,
        1 <= result.0[0].len() <= 50,
        forall|r: int| 0 <= r < result.0.len() ==> #[trigger] result.0[r].len() == result.0[0].len(),
        forall|r: int, c: int| 0 <= r < result.0.len() && 0 <= c < result.0[r].len() ==> 1 <= #[trigger] result.0[r][c] <= 100,
        0 <= (result.1 as int),
        (result.1 as int) < result.0.len(),
        0 <= (result.2 as int),
        (result.2 as int) < result.0[0].len(),
        1 <= (result.3 as int),
        (result.3 as int) <= result.0.len() - (result.1 as int),
        (result.3 as int) <= result.0[0].len() - (result.2 as int),
{
    if mutation_kind == 0 {
        // identity
        (grid, x, y, k)
    } else if mutation_kind == 1 && k > 1 {
        // shrink k by 1
        (grid, x, y, k - 1)
    } else if mutation_kind == 2 {
        // grow k by 1 if possible
        let rows = grid.len() as i32;
        let cols = grid[0].len() as i32;
        if k + 1 <= rows - x && k + 1 <= cols - y {
            (grid, x, y, k + 1)
        } else {
            (grid, x, y, k)
        }
    } else if mutation_kind == 3 && x > 0 {
        // shift x up by 1
        proof {
            assert((x - 1) as int >= 0);
            assert(((x - 1) as int) < grid.len() as int);
            assert((k as int) <= (grid.len() as int) - ((x - 1) as int));
        }
        (grid, x - 1, y, k)
    } else if mutation_kind == 4 {
        // shift x down by 1 if possible
        let rows = grid.len() as i32;
        if x + 1 < rows && k <= rows - (x + 1) {
            (grid, x + 1, y, k)
        } else {
            (grid, x, y, k)
        }
    } else if mutation_kind == 5 && y > 0 {
        // shift y left by 1
        proof {
            assert((y - 1) as int >= 0);
            assert(((y - 1) as int) < grid[0].len() as int);
            assert((k as int) <= (grid[0].len() as int) - ((y - 1) as int));
        }
        (grid, x, y - 1, k)
    } else if mutation_kind == 6 {
        // shift y right by 1 if possible
        let cols = grid[0].len() as i32;
        if y + 1 < cols && k <= cols - (y + 1) {
            (grid, x, y + 1, k)
        } else {
            (grid, x, y, k)
        }
    } else if mutation_kind == 7 {
        // set k to 1 (minimal square)
        (grid, x, y, 1)
    } else if mutation_kind == 8 {
        // set x=0, y=0, k=1 (top-left corner, minimal)
        (grid, 0, 0, 1)
    } else if mutation_kind == 9 {
        // x=0, k stays (top-aligned)
        proof {
            assert(0 <= 0i32);
            assert((0i32 as int) < grid.len() as int);
            assert((k as int) <= (grid.len() as int) - (0i32 as int));
        }
        (grid, 0i32, y, k)
    } else if mutation_kind == 10 {
        // y=0, k stays (left-aligned)
        proof {
            assert(0 <= 0i32);
            assert((0i32 as int) < grid[0].len() as int);
            assert((k as int) <= (grid[0].len() as int) - (0i32 as int));
        }
        (grid, x, 0i32, k)
    } else if mutation_kind == 11 {
        // max k for current x,y
        let rows = grid.len() as i32;
        let cols = grid[0].len() as i32;
        let max_k_r = rows - x;
        let max_k_c = cols - y;
        let new_k = if max_k_r <= max_k_c { max_k_r } else { max_k_c };
        proof {
            assert(1 <= new_k as int);
            assert((new_k as int) <= (grid.len() as int) - (x as int));
            assert((new_k as int) <= (grid[0].len() as int) - (y as int));
        }
        (grid, x, y, new_k)
    } else {
        // fallback: identity
        (grid, x, y, k)
    }
}

} // verus!

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }

    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0
    }

    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        assert!(lo <= hi);
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

struct Solution;
include!("../code.rs");

extern crate serde_json;
use serde_json::json;

fn random_grid(rng: &mut Rng, rows: usize, cols: usize) -> Vec<Vec<i32>> {
    let mut grid = Vec::with_capacity(rows);
    for _ in 0..rows {
        let mut row = Vec::with_capacity(cols);
        for _ in 0..cols {
            row.push(rng.gen_range_i64(1, 100) as i32);
        }
        grid.push(row);
    }
    grid
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(3643);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut emitted = 0usize;

    let mut emit = |grid: Vec<Vec<i32>>, x: i32, y: i32, k: i32,
                    seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>,
                    emitted: &mut usize| {
        if *emitted >= count { return; }
        let key = format!("{:?},{},{},{}", grid, x, y, k);
        if !seen.insert(key) { return; }
        let result = Solution::reverse_submatrix(grid.clone(), x, y, k);
        writeln!(out, "{}", json!({
            "input": {"grid": grid, "x": x, "y": y, "k": k},
            "output": result
        })).unwrap();
        *emitted += 1;
    };

    // Example 1 from description.md
    {
        let grid = vec![
            vec![1,2,3,4], vec![5,6,7,8], vec![9,10,11,12], vec![13,14,15,16]
        ];
        let (g, xv, yv, kv) = generate_test_case(grid, 1, 0, 3, 0);
        emit(g, xv, yv, kv, &mut seen, &mut out, &mut emitted);
    }

    // Example 2 from description.md
    {
        let grid = vec![vec![3,4,2,3], vec![2,3,4,2]];
        let (g, xv, yv, kv) = generate_test_case(grid, 0, 2, 2, 0);
        emit(g, xv, yv, kv, &mut seen, &mut out, &mut emitted);
    }

    // Seed grids with all mutations
    let seed_configs: Vec<(usize, usize, i32, i32, i32)> = vec![
        // (rows, cols, x, y, k)
        (1, 1, 0, 0, 1),       // minimal 1x1
        (2, 2, 0, 0, 2),       // 2x2 full
        (2, 2, 0, 0, 1),       // 2x2 corner
        (3, 3, 0, 0, 3),       // 3x3 full
        (3, 3, 1, 1, 1),       // 3x3 center
        (4, 4, 1, 0, 3),       // 4x4, example-like
        (5, 5, 0, 0, 5),       // 5x5 full
        (5, 5, 2, 2, 3),       // 5x5 center sub
        (50, 50, 0, 0, 50),    // max full
        (50, 50, 25, 25, 25),  // max, sub in corner
        (50, 50, 0, 0, 1),     // max, minimal k
        (1, 50, 0, 0, 1),      // single row
        (50, 1, 0, 0, 1),      // single col
        (10, 10, 3, 3, 4),     // medium
    ];

    let mutation_kinds: Vec<u8> = (0..=11).collect();

    for &(rows, cols, x, y, k) in &seed_configs {
        let grid = random_grid(&mut rng, rows, cols);
        for &mk in &mutation_kinds {
            let (g, xv, yv, kv) = generate_test_case(grid.clone(), x, y, k, mk);
            emit(g, xv, yv, kv, &mut seen, &mut out, &mut emitted);
        }
    }

    // Random test cases with size classes
    while emitted < count {
        let (rows, cols) = match emitted % 5 {
            0 => (rng.gen_range_usize(1, 3), rng.gen_range_usize(1, 3)),       // tiny
            1 => (rng.gen_range_usize(2, 8), rng.gen_range_usize(2, 8)),       // small
            2 => (rng.gen_range_usize(5, 20), rng.gen_range_usize(5, 20)),     // medium
            3 => (rng.gen_range_usize(20, 40), rng.gen_range_usize(20, 40)),   // large
            _ => (rng.gen_range_usize(40, 50), rng.gen_range_usize(40, 50)),   // max
        };
        let grid = random_grid(&mut rng, rows, cols);
        let max_k = std::cmp::min(rows, cols);
        let k = rng.gen_range_usize(1, max_k) as i32;
        let x = rng.gen_range_usize(0, rows - k as usize) as i32;
        let y = rng.gen_range_usize(0, cols - k as usize) as i32;
        let mk = rng.gen_range_usize(0, 11) as u8;
        let (g, xv, yv, kv) = generate_test_case(grid, x, y, k, mk);
        emit(g, xv, yv, kv, &mut seen, &mut out, &mut emitted);
    }
}
