use vstd::prelude::*;

verus! {

pub fn generate_test_case(grid: Vec<Vec<i32>>, mutation_kind: u8) -> (result: Vec<Vec<i32>>)
    requires
        1 <= grid.len() <= 50,
        1 <= grid[0].len() <= 50,
        forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
        forall |r: int, c: int|
            0 <= r < grid.len() && 0 <= c < grid[r].len() ==> 0 <= #[trigger] grid[r][c] < 2500,
    ensures
        1 <= result.len() <= 50,
        1 <= result[0].len() <= 50,
        forall |r: int| 0 <= r < result.len() ==> #[trigger] result[r].len() == result[0].len(),
        forall |r: int, c: int|
            0 <= r < result.len() && 0 <= c < result[r].len() ==> 0 <= #[trigger] result[r][c] < 2500,
{
    if mutation_kind == 0 {
        // identity
        grid
    } else if mutation_kind == 1 && grid.len() > 1 {
        // remove last row (shrink)
        let mut g = grid;
        g.pop();
        g
    } else if mutation_kind == 2 {
        // replace first row with all zeros
        let n = grid[0].len();
        let mut new_row: Vec<i32> = Vec::new();
        let mut c: usize = 0;
        while c < n
            invariant
                0 <= c <= n,
                new_row.len() == c as int,
                n == grid[0int].len(),
                1 <= n <= 50,
                forall |j: int| 0 <= j < c ==> #[trigger] new_row[j] == 0i32,
                forall |j: int| 0 <= j < c ==> 0 <= #[trigger] new_row[j] < 2500,
            decreases n - c,
        {
            new_row.push(0i32);
            c += 1;
        }
        let mut g = grid;
        g.set(0, new_row);
        g
    } else if mutation_kind == 3 {
        // replace first row with max boundary (2499)
        let n = grid[0].len();
        let mut new_row: Vec<i32> = Vec::new();
        let mut c: usize = 0;
        while c < n
            invariant
                0 <= c <= n,
                new_row.len() == c as int,
                n == grid[0int].len(),
                1 <= n <= 50,
                forall |j: int| 0 <= j < c ==> #[trigger] new_row[j] == 2499i32,
                forall |j: int| 0 <= j < c ==> 0 <= #[trigger] new_row[j] < 2500,
            decreases n - c,
        {
            new_row.push(2499i32);
            c += 1;
        }
        let mut g = grid;
        g.set(0, new_row);
        g
    } else if mutation_kind == 4 && grid.len() < 50 {
        // append a row of zeros (grow)
        let n = grid[0].len();
        let mut new_row: Vec<i32> = Vec::new();
        let mut c: usize = 0;
        while c < n
            invariant
                0 <= c <= n,
                new_row.len() == c as int,
                n == grid[0int].len(),
                1 <= n <= 50,
                forall |j: int| 0 <= j < c ==> #[trigger] new_row[j] == 0i32,
                forall |j: int| 0 <= j < c ==> 0 <= #[trigger] new_row[j] < 2500,
            decreases n - c,
        {
            new_row.push(0i32);
            c += 1;
        }
        let mut g = grid;
        g.push(new_row);
        g
    } else if mutation_kind == 5 {
        // replace first row with ascending 0, 1, 2, ..., n-1
        let n = grid[0].len();
        let mut new_row: Vec<i32> = Vec::new();
        let mut c: usize = 0;
        while c < n
            invariant
                0 <= c <= n,
                new_row.len() == c as int,
                n == grid[0int].len(),
                1 <= n <= 50,
                forall |j: int| 0 <= j < c ==> #[trigger] new_row[j] == j as i32,
                forall |j: int| 0 <= j < c ==> 0 <= #[trigger] new_row[j] < 2500,
            decreases n - c,
        {
            new_row.push(c as i32);
            c += 1;
        }
        let mut g = grid;
        g.set(0, new_row);
        g
    } else if mutation_kind == 6 {
        // replace first row with descending n-1, n-2, ..., 0
        let n = grid[0].len();
        let mut new_row: Vec<i32> = Vec::new();
        let mut c: usize = 0;
        while c < n
            invariant
                0 <= c <= n,
                new_row.len() == c as int,
                n == grid[0int].len(),
                1 <= n <= 50,
                forall |j: int| 0 <= j < c ==> #[trigger] new_row[j] == (n as int - 1 - j) as i32,
                forall |j: int| 0 <= j < c ==> 0 <= #[trigger] new_row[j] < 2500,
            decreases n - c,
        {
            new_row.push((n - 1 - c) as i32);
            c += 1;
        }
        let mut g = grid;
        g.set(0, new_row);
        g
    } else {
        // fallback: identity
        grid
    }
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
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

struct Solution;
include!("../code.rs");

fn random_grid(rng: &mut Rng, m: usize, n: usize, lo: i32, hi: i32) -> Vec<Vec<i32>> {
    let mut grid = Vec::with_capacity(m);
    for _ in 0..m {
        let mut row = Vec::with_capacity(n);
        for _ in 0..n {
            row.push(rng.gen_range_i64(lo as i64, hi as i64) as i32);
        }
        grid.push(row);
    }
    grid
}

fn mutate(grid: Vec<Vec<i32>>, mk: u8) -> Vec<Vec<i32>> {
    generate_test_case(grid, mk)
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(3402);
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
        let output = Solution::minimum_operations(grid.clone());
        writeln!(out, "{}", json!({"input": {"grid": grid}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<Vec<i32>>> = vec![
        vec![vec![3,2], vec![1,3], vec![3,4], vec![0,1]],
        vec![vec![3,2,1], vec![2,1,0], vec![1,2,3]],
    ];
    for ex in &examples {
        emit(ex.clone(), &mut seen, &mut out, &mut count);
    }

    // Seed grids: hand-crafted interesting inputs
    let seeds: Vec<Vec<Vec<i32>>> = vec![
        vec![vec![0]],                                          // 1x1 zero
        vec![vec![2499]],                                       // 1x1 max
        vec![vec![0, 0], vec![0, 0]],                           // 2x2 all zeros
        vec![vec![2499, 2499], vec![2499, 2499]],               // 2x2 all max
        vec![vec![1, 2], vec![3, 4]],                           // 2x2 already increasing cols
        vec![vec![4, 3], vec![2, 1]],                           // 2x2 decreasing cols
        vec![vec![5, 5], vec![5, 5], vec![5, 5]],               // 3x2 uniform
        vec![vec![0], vec![0], vec![0], vec![0], vec![0]],      // 5x1 all zeros
        vec![vec![1, 2, 3], vec![4, 5, 6], vec![7, 8, 9]],     // 3x3 increasing
        vec![vec![9, 8, 7], vec![6, 5, 4], vec![3, 2, 1]],     // 3x3 decreasing
        vec![vec![0, 2499], vec![2499, 0]],                     // 2x2 mixed extremes
        vec![vec![100], vec![100], vec![100]],                  // 3x1 uniform
        vec![vec![0, 0, 0, 0, 0]],                              // 1x5 zeros
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6];

    // Apply every mutation to every seed
    for s in &seeds {
        for &mk in &mutation_kinds {
            let result = mutate(s.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Size classes with random mutations
    for i in 0..60 {
        if count >= target_count { break; }
        let (m, n) = match i % 5 {
            0 => (rng.gen_range_usize(1, 2), rng.gen_range_usize(1, 2)),          // tiny
            1 => (rng.gen_range_usize(1, 5), rng.gen_range_usize(1, 5)),          // small
            2 => (rng.gen_range_usize(5, 15), rng.gen_range_usize(5, 15)),        // medium
            3 => (rng.gen_range_usize(15, 35), rng.gen_range_usize(15, 35)),      // large
            _ => (rng.gen_range_usize(35, 50), rng.gen_range_usize(35, 50)),      // max
        };
        let grid = random_grid(&mut rng, m, n, 0, 2499);
        let mk = rng.gen_range_usize(0, 6) as u8;
        let result = mutate(grid, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }

    // Fill remaining with random grids (identity mutation)
    while count < target_count {
        let m = rng.gen_range_usize(1, 50);
        let n = rng.gen_range_usize(1, 50);
        let grid = random_grid(&mut rng, m, n, 0, 2499);
        emit(mutate(grid, 0), &mut seen, &mut out, &mut count);
    }
}
