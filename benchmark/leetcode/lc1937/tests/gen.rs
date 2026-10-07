use vstd::prelude::*;

verus! {

pub fn generate_test_case(points: Vec<Vec<i32>>, mutation_kind: u8) -> (result: Vec<Vec<i32>>)
    requires
        1 <= points.len() <= 100_000,
        1 <= points[0].len() <= 100_000,
        points.len() * points[0].len() <= 100_000,
        forall|r: int|
            0 <= r < points.len() ==> (#[trigger] points[r]).len() == points[0].len(),
        forall|r: int, c: int|
            0 <= r < points.len() && 0 <= c < points[0].len()
                ==> 0 <= #[trigger] points[r][c] <= 100_000,
    ensures
        1 <= result.len() <= 100_000,
        1 <= result[0].len() <= 100_000,
        result.len() * result[0].len() <= 100_000,
        forall|r: int|
            0 <= r < result.len() ==> (#[trigger] result[r]).len() == result[0].len(),
        forall|r: int, c: int|
            0 <= r < result.len() && 0 <= c < result[0].len()
                ==> 0 <= #[trigger] result[r][c] <= 100_000,
{
    if mutation_kind == 0 {
        // identity
        points
    } else if mutation_kind == 1 {
        // set cell (0,0) to 0
        let mut m = points;
        let mut row0 = m[0].clone();
        row0.set(0, 0i32);
        m.set(0, row0);
        m
    } else if mutation_kind == 2 {
        // set cell (0,0) to 100_000
        let mut m = points;
        let mut row0 = m[0].clone();
        row0.set(0, 100_000i32);
        m.set(0, row0);
        m
    } else if mutation_kind == 3 {
        // set last cell of first row to 0
        let mut m = points;
        let mut row0 = m[0].clone();
        let last = row0.len() - 1;
        row0.set(last, 0i32);
        m.set(0, row0);
        m
    } else if mutation_kind == 4 {
        // set last cell of first row to 100_000
        let mut m = points;
        let mut row0 = m[0].clone();
        let last = row0.len() - 1;
        row0.set(last, 100_000i32);
        m.set(0, row0);
        m
    } else if mutation_kind == 5 && points[0][0] < 100_000 {
        // nudge cell (0,0) up by 1
        let mut m = points;
        let mut row0 = m[0].clone();
        row0.set(0, row0[0] + 1);
        m.set(0, row0);
        m
    } else if mutation_kind == 6 && points[0][0] > 0 {
        // nudge cell (0,0) down by 1
        let mut m = points;
        let mut row0 = m[0].clone();
        row0.set(0, row0[0] - 1);
        m.set(0, row0);
        m
    } else if mutation_kind == 7 {
        // set first row to all zeros
        let n_cols = points[0].len();
        let mut m = points;
        let mut row0: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n_cols
            invariant
                0 <= j <= n_cols,
                row0.len() == j,
                1 <= n_cols <= 100_000,
                forall|k: int| 0 <= k < j ==> #[trigger] row0[k] == 0,
            decreases n_cols - j,
        {
            row0.push(0i32);
            j += 1;
        }
        m.set(0, row0);
        m
    } else if mutation_kind == 8 {
        // set first row to all 100_000
        let n_cols = points[0].len();
        let mut m = points;
        let mut row0: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n_cols
            invariant
                0 <= j <= n_cols,
                row0.len() == j,
                1 <= n_cols <= 100_000,
                forall|k: int| 0 <= k < j ==> #[trigger] row0[k] == 100_000,
            decreases n_cols - j,
        {
            row0.push(100_000i32);
            j += 1;
        }
        m.set(0, row0);
        m
    } else {
        // fallback: identity
        points
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

fn mutate(points: Vec<Vec<i32>>, mutation_kind: u8) -> Vec<Vec<i32>> {
    generate_test_case(points, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_matrix(rng: &mut Rng, m: usize, n: usize, val_lo: i64, val_hi: i64) -> Vec<Vec<i32>> {
    let mut mat = Vec::with_capacity(m);
    for _ in 0..m {
        let mut row = Vec::with_capacity(n);
        for _ in 0..n {
            row.push(rng.gen_range_i64(val_lo, val_hi) as i32);
        }
        mat.push(row);
    }
    mat
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1937);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut total = 0usize;

    let mut emit = |points: Vec<Vec<i32>>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, total: &mut usize| {
        if *total >= count { return; }
        let key = format!("{:?}", points);
        if !seen.insert(key) { return; }
        let output = Solution::max_points(points.clone());
        writeln!(out, "{}", json!({"input": {"points": points}, "output": output})).unwrap();
        *total += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<Vec<i32>>> = vec![
        vec![vec![1,2,3], vec![1,5,1], vec![3,1,1]],
        vec![vec![1,5], vec![2,3], vec![4,2]],
    ];
    for ex in examples {
        for mk in 0..=8u8 {
            let result = mutate(ex.clone(), mk);
            emit(result, &mut seen, &mut out, &mut total);
        }
    }

    // Edge cases: single cell
    emit(mutate(vec![vec![0]], 0), &mut seen, &mut out, &mut total);
    emit(mutate(vec![vec![100_000]], 0), &mut seen, &mut out, &mut total);

    // Edge case: single row
    emit(mutate(vec![vec![1, 2, 3, 4, 5]], 0), &mut seen, &mut out, &mut total);

    // Edge case: single column
    emit(mutate(vec![vec![10], vec![20], vec![30]], 0), &mut seen, &mut out, &mut total);

    // Edge cases: all same values
    let all_zeros = vec![vec![0, 0, 0]; 3];
    emit(mutate(all_zeros, 0), &mut seen, &mut out, &mut total);
    let all_max = vec![vec![100_000, 100_000]; 2];
    emit(mutate(all_max, 0), &mut seen, &mut out, &mut total);

    // Mutation sweep with varied seed matrices
    let seed_dims: Vec<(usize, usize)> = vec![
        (1, 1), (1, 5), (5, 1), (2, 3), (3, 3), (4, 4), (10, 10),
        (1, 100), (100, 1), (5, 20), (20, 5), (50, 50),
    ];
    for &(m, n) in &seed_dims {
        let mat = random_matrix(&mut rng, m, n, 0, 100_000);
        for mk in 0..=8u8 {
            let result = mutate(mat.clone(), mk);
            emit(result, &mut seen, &mut out, &mut total);
        }
    }

    // Diverse size classes with random mutations
    while total < count {
        // Pick a size class
        let class = rng.gen_range_usize(0, 5);
        let (m, n) = match class {
            0 => {
                // tiny: 1-3 rows/cols
                let m = rng.gen_range_usize(1, 3);
                let n = rng.gen_range_usize(1, 3);
                (m, n)
            }
            1 => {
                // small: 1-10
                let m = rng.gen_range_usize(1, 10);
                let max_n = 100_000 / m;
                let n = rng.gen_range_usize(1, max_n.min(10));
                (m, n)
            }
            2 => {
                // medium
                let m = rng.gen_range_usize(5, 50);
                let max_n = 100_000 / m;
                let n = rng.gen_range_usize(1, max_n.min(50));
                (m, n)
            }
            3 => {
                // large square-ish
                let m = rng.gen_range_usize(50, 316);
                let max_n = 100_000 / m;
                let n = rng.gen_range_usize(1, max_n.min(316));
                (m, n)
            }
            4 => {
                // tall and narrow
                let m = rng.gen_range_usize(1000, 100_000);
                let max_n = 100_000 / m;
                let n = rng.gen_range_usize(1, max_n.max(1));
                (m, n)
            }
            _ => {
                // wide and short
                let n = rng.gen_range_usize(1000, 100_000);
                let max_m = 100_000 / n;
                let m = rng.gen_range_usize(1, max_m.max(1));
                (m, n)
            }
        };

        // Vary value distribution
        let val_class = rng.gen_range_usize(0, 4);
        let (lo, hi): (i64, i64) = match val_class {
            0 => (0, 100_000),       // full range
            1 => (0, 10),            // small values
            2 => (90_000, 100_000),  // large values
            3 => (0, 0),             // all zeros
            _ => (50_000, 50_000),   // all same
        };

        let mat = random_matrix(&mut rng, m, n, lo, hi);
        let mk = rng.gen_range_usize(0, 8) as u8;
        let result = mutate(mat, mk);
        emit(result, &mut seen, &mut out, &mut total);
    }
}
