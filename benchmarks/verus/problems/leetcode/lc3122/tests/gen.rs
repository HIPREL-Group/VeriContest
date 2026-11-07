use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    num_rows: usize,
    num_cols: usize,
    fill_value: i32,
    alt_value: i32,
    mutation_kind: u8,
) -> (grid: Vec<Vec<i32>>)
    requires
        1 <= num_rows <= 1000,
        1 <= num_cols <= 1000,
        0 <= fill_value <= 9,
        0 <= alt_value <= 9,
    ensures
        1 <= grid.len() <= 1000,
        1 <= grid[0].len() <= 1000,
        forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
        forall |r: int, c: int| 0 <= r < grid.len() && 0 <= c < grid[r].len() ==> 0 <= #[trigger] grid[r][c] <= 9,
{
    let mut grid: Vec<Vec<i32>> = Vec::new();
    let mut r: usize = 0;
    while r < num_rows
        invariant
            0 <= r <= num_rows,
            grid.len() == r,
            1 <= num_cols <= 1000,
            1 <= num_rows <= 1000,
            0 <= fill_value <= 9,
            0 <= alt_value <= 9,
            forall |i: int| 0 <= i < r as int ==> (#[trigger] grid[i]).len() == num_cols,
            forall |i: int, j: int| 0 <= i < r as int && 0 <= j < grid[i].len() ==> 0 <= #[trigger] grid[i][j] <= 9,
        decreases num_rows - r,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut c: usize = 0;
        while c < num_cols
            invariant
                0 <= c <= num_cols,
                row.len() == c,
                0 <= fill_value <= 9,
                0 <= alt_value <= 9,
                num_cols <= 1000,
                forall |j: int| 0 <= j < c as int ==> 0 <= #[trigger] row[j] <= 9,
            decreases num_cols - c,
        {
            let val: i32 = if mutation_kind == 0 {
                fill_value
            } else if mutation_kind == 1 && c % 2 == 0 {
                fill_value
            } else if mutation_kind == 1 {
                alt_value
            } else if mutation_kind == 2 {
                ((fill_value as usize + c) % 10) as i32
            } else if mutation_kind == 3 {
                0i32
            } else if mutation_kind == 4 {
                9i32
            } else if mutation_kind == 5 && c == 0 {
                alt_value
            } else if mutation_kind == 5 {
                fill_value
            } else {
                fill_value
            };
            row.push(val);
            c = c + 1;
        }
        grid.push(row);
        r = r + 1;
    }
    grid
}

} // verus!

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
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

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(3122);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |grid: Vec<Vec<i32>>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        let key = format!("{:?}", grid);
        if !seen.insert(key) { return; }
        let result = Solution::minimum_operations(grid.clone());
        writeln!(out, "{}", json!({"input": {"grid": grid}, "output": result})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<Vec<i32>>> = vec![
        vec![vec![1,0,2], vec![1,0,2]],
        vec![vec![1,1,1], vec![0,0,0]],
        vec![vec![1], vec![2], vec![3]],
    ];
    for ex in examples {
        emit(ex, &mut seen, &mut out, &mut count);
    }

    // Systematic: size classes × fill values × mutation kinds
    let size_classes: Vec<(usize, usize)> = vec![
        (1, 1), (1, 2), (2, 1), (2, 2), (3, 3),
        (1, 10), (10, 1), (5, 5), (10, 10),
        (1, 100), (100, 1), (50, 50),
        (1, 1000), (1000, 1), (100, 100),
    ];
    let fill_values: Vec<i32> = vec![0, 1, 5, 9];
    let alt_values: Vec<i32> = vec![0, 3, 7, 9];
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5];

    for &(nr, nc) in &size_classes {
        for &fv in &fill_values {
            for &mk in &mutation_kinds {
                if count >= target { break; }
                let av = alt_values[count % alt_values.len()];
                let grid = generate_test_case(nr, nc, fv, av, mk);
                emit(grid, &mut seen, &mut out, &mut count);
            }
        }
    }

    // Random inputs to fill remaining
    while count < target {
        let nr = match count % 5 {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(10, 50),
            3 => rng.gen_range_usize(50, 200),
            _ => rng.gen_range_usize(200, 1000),
        };
        let nc = match count % 5 {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(10, 50),
            3 => rng.gen_range_usize(50, 200),
            _ => rng.gen_range_usize(1, 10),
        };
        let fv = rng.gen_range_i64(0, 9) as i32;
        let av = rng.gen_range_i64(0, 9) as i32;
        let mk = rng.gen_range_usize(0, 5) as u8;
        let grid = generate_test_case(nr, nc, fv, av, mk);
        emit(grid, &mut seen, &mut out, &mut count);
    }
}
