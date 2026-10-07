use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_grid: Vec<Vec<i32>>, mutation_kind: u8) -> (grid: Vec<Vec<i32>>)
    requires
        2 <= seed_grid.len() <= 1000,
        2 <= seed_grid[0].len() <= 1000,
        4 <= seed_grid.len() * seed_grid[0].len() <= 100000,
        forall |i: int| 0 <= i < seed_grid.len() ==> #[trigger] seed_grid[i].len() == seed_grid[0].len(),
        forall |i: int, j: int| 0 <= i < seed_grid.len() && 0 <= j < seed_grid[i].len() ==> 1 <= #[trigger] seed_grid[i][j] <= 100000,
    ensures
        2 <= grid.len() <= 1000,
        2 <= grid[0].len() <= 1000,
        4 <= grid.len() * grid[0].len() <= 100000,
        forall |i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == grid[0].len(),
        forall |i: int, j: int| 0 <= i < grid.len() && 0 <= j < grid[i].len() ==> 1 <= #[trigger] grid[i][j] <= 100000,
{
    if mutation_kind == 0 {
        // identity
        seed_grid
    } else if mutation_kind == 1 {
        // set grid[0][0] to 1 (min boundary)
        let mut g = seed_grid;
        let mut row0 = g[0].clone();
        row0.set(0, 1i32);
        g.set(0, row0);
        g
    } else if mutation_kind == 2 {
        // set grid[0][0] to 100000 (max boundary)
        let mut g = seed_grid;
        let mut row0 = g[0].clone();
        row0.set(0, 100000i32);
        g.set(0, row0);
        g
    } else if mutation_kind == 3 && seed_grid[0][0] < 100000 {
        // nudge grid[0][0] up
        let mut g = seed_grid;
        let mut row0 = g[0].clone();
        let v = row0[0];
        row0.set(0, (v + 1) as i32);
        g.set(0, row0);
        g
    } else if mutation_kind == 4 && seed_grid[0][0] > 1 {
        // nudge grid[0][0] down
        let mut g = seed_grid;
        let mut row0 = g[0].clone();
        let v = row0[0];
        row0.set(0, (v - 1) as i32);
        g.set(0, row0);
        g
    } else if mutation_kind == 5 {
        // set last cell of last row to 1
        let mut g = seed_grid;
        let last_r = g.len() - 1;
        let mut row = g[last_r].clone();
        let last_c = row.len() - 1;
        row.set(last_c, 1i32);
        g.set(last_r, row);
        g
    } else if mutation_kind == 6 {
        // set last cell of last row to 100000
        let mut g = seed_grid;
        let last_r = g.len() - 1;
        let mut row = g[last_r].clone();
        let last_c = row.len() - 1;
        row.set(last_c, 100000i32);
        g.set(last_r, row);
        g
    } else if mutation_kind == 7 {
        // set grid[0][0] to 50000 (mid value)
        let mut g = seed_grid;
        let mut row0 = g[0].clone();
        row0.set(0, 50000i32);
        g.set(0, row0);
        g
    } else {
        // fallback: identity
        seed_grid
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

fn mutate(seed_grid: Vec<Vec<i32>>, mutation_kind: u8) -> Vec<Vec<i32>> {
    generate_test_case(seed_grid, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_grid(rng: &mut Rng, rows: usize, cols: usize) -> Vec<Vec<i32>> {
    let mut grid = Vec::with_capacity(rows);
    for _ in 0..rows {
        let mut row = Vec::with_capacity(cols);
        for _ in 0..cols {
            row.push(rng.gen_range_i64(1, 100000) as i32);
        }
        grid.push(row);
    }
    grid
}

fn valid_dims(rng: &mut Rng, size_class: usize) -> (usize, usize) {
    // Generate valid (rows, cols) pairs satisfying:
    // 2 <= rows, cols <= 1000 and 4 <= rows*cols <= 100000
    match size_class {
        0 => (2, 2),                                              // minimum
        1 => {                                                    // small
            let r = rng.gen_range_usize(2, 5);
            let c = rng.gen_range_usize(2, 5);
            (r, c)
        }
        2 => {                                                    // medium
            let r = rng.gen_range_usize(2, 20);
            let max_c = (100000 / r).min(1000);
            let c = rng.gen_range_usize(2, max_c);
            (r, c)
        }
        3 => {                                                    // large
            let r = rng.gen_range_usize(10, 100);
            let max_c = (100000 / r).min(1000);
            let c = rng.gen_range_usize(2, max_c);
            (r, c)
        }
        _ => {                                                    // max-ish
            let r = rng.gen_range_usize(50, 316);
            let max_c = (100000 / r).min(1000);
            let c = rng.gen_range_usize(2, max_c);
            (r, c)
        }
    }
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(3148);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |grid: Vec<Vec<i32>>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count {
            return;
        }
        let key = format!("{:?}", grid);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::max_score(grid.clone());
        writeln!(out, "{}", json!({
            "input": {"grid": grid},
            "output": output
        })).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<Vec<i32>>> = vec![
        vec![vec![9,5,7,3], vec![8,9,6,1], vec![6,7,14,3], vec![2,5,3,1]],
        vec![vec![4,3,2], vec![3,2,1]],
    ];
    for ex in examples {
        emit(ex, &mut seen, &mut out, &mut count);
    }

    // Hand-crafted seed grids for diversity
    let seed_grids: Vec<Vec<Vec<i32>>> = vec![
        vec![vec![1, 1], vec![1, 1]],                           // all minimum
        vec![vec![100000, 100000], vec![100000, 100000]],       // all maximum
        vec![vec![1, 100000], vec![100000, 1]],                 // alternating extremes
        vec![vec![1, 2, 3], vec![4, 5, 6]],                     // ascending
        vec![vec![6, 5, 4], vec![3, 2, 1]],                     // descending
        vec![vec![50000, 50000], vec![50000, 50000]],           // all mid
        vec![vec![1, 2], vec![3, 4], vec![5, 6]],               // tall grid
        vec![vec![1, 2, 3, 4, 5], vec![6, 7, 8, 9, 10]],       // wide grid
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7];

    // Apply every mutation to every seed grid
    for sg in &seed_grids {
        for &mk in &mutation_kinds {
            let result = mutate(sg.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Generate diverse random grids with mutations
    while count < target_count {
        let size_class = rng.gen_range_usize(0, 4);
        let (rows, cols) = valid_dims(&mut rng, size_class);
        let grid = random_grid(&mut rng, rows, cols);

        // Boundary value injection (~20% of cases)
        let mut grid = grid;
        let inject = rng.gen_range_usize(0, 4);
        if inject == 0 {
            // inject boundary values in a few cells
            let ri = rng.gen_range_usize(0, rows - 1);
            let ci = rng.gen_range_usize(0, cols - 1);
            let bv = if rng.gen_range_usize(0, 1) == 0 { 1 } else { 100000 };
            grid[ri][ci] = bv;
        }

        let mk = rng.gen_range_usize(0, 7) as u8;
        let result = mutate(grid, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }
}
