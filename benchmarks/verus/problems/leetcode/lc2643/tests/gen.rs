use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    num_rows: usize,
    num_cols: usize,
    hot_row: usize,
    mutation_kind: u8,
) -> (mat: Vec<Vec<i32>>)
    requires
        1 <= num_rows <= 100,
        1 <= num_cols <= 100,
        hot_row < num_rows,
    ensures
        mat.len() > 0,
        mat.len() <= 2147483647usize,
{
    let mut mat: Vec<Vec<i32>> = Vec::new();
    let mut r: usize = 0;
    while r < num_rows
        invariant
            0 <= r <= num_rows,
            mat.len() == r,
            1 <= num_rows <= 100,
        decreases num_rows - r,
    {
        let fill: i32 = if r == hot_row { 1i32 } else { 0i32 };
        let mut row: Vec<i32> = Vec::new();
        let mut c: usize = 0;
        while c < num_cols
            invariant
                0 <= c <= num_cols,
                row.len() == c,
            decreases num_cols - c,
        {
            row.push(fill);
            c += 1;
        }
        mat.push(row);
        r += 1;
    }

    if mutation_kind == 1 && mat.len() < 100 {
        // grow: add an extra row of zeros
        let mut extra: Vec<i32> = Vec::new();
        let mut c: usize = 0;
        while c < num_cols
            invariant
                0 <= c <= num_cols,
                extra.len() == c,
            decreases num_cols - c,
        {
            extra.push(0i32);
            c += 1;
        }
        mat.push(extra);
    } else if mutation_kind == 2 && mat.len() > 1 {
        // shrink: remove last row
        mat.pop();
    } else if mutation_kind == 3 && mat.len() < 100 {
        // grow: add an extra row of ones
        let mut extra: Vec<i32> = Vec::new();
        let mut c: usize = 0;
        while c < num_cols
            invariant
                0 <= c <= num_cols,
                extra.len() == c,
            decreases num_cols - c,
        {
            extra.push(1i32);
            c += 1;
        }
        mat.push(extra);
    }
    // mutation_kind == 0 or fallback: identity (constructed matrix as-is)

    mat
}

} // verus!

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

fn random_binary_matrix(rng: &mut Rng, rows: usize, cols: usize) -> Vec<Vec<i32>> {
    let mut mat = Vec::with_capacity(rows);
    for _ in 0..rows {
        let mut row = Vec::with_capacity(cols);
        for _ in 0..cols {
            row.push(rng.gen_range_i64(0, 1) as i32);
        }
        mat.push(row);
    }
    mat
}

fn main() {
    use std::io::Write;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);

    let mut n = 0usize;

    let mut emit = |mat: Vec<Vec<i32>>, out: &mut std::io::BufWriter<std::fs::File>, n: &mut usize| {
        if *n >= count {
            return;
        }
        let result = Solution::row_and_maximum_ones(mat.clone());
        writeln!(out, "{}", json!({"input": {"mat": mat}, "output": result})).unwrap();
        *n += 1;
    };

    // Example inputs from description.md
    emit(vec![vec![0, 1], vec![1, 0]], &mut out, &mut n);
    emit(vec![vec![0, 0, 0], vec![0, 1, 1]], &mut out, &mut n);
    emit(vec![vec![0, 0], vec![1, 1], vec![0, 0]], &mut out, &mut n);

    // Verified generator: diverse (num_rows, num_cols, hot_row, mutation_kind)
    let row_sizes: Vec<usize> = vec![1, 2, 3, 5, 10, 50, 100];
    let col_sizes: Vec<usize> = vec![1, 2, 3, 5, 10, 50, 100];
    let mutations: Vec<u8> = vec![0, 1, 2, 3];

    for &nr in &row_sizes {
        for &nc in &col_sizes {
            for &mk in &mutations {
                if n >= count {
                    break;
                }
                let hot = rng.gen_range_usize(0, nr - 1);
                let mat = generate_test_case(nr, nc, hot, mk);
                emit(mat, &mut out, &mut n);
            }
        }
    }

    // Random binary matrices of varied sizes
    while n < count {
        let nr = match n % 5 {
            0 => rng.gen_range_usize(1, 3),    // tiny
            1 => rng.gen_range_usize(1, 10),   // small
            2 => rng.gen_range_usize(11, 30),  // medium
            3 => rng.gen_range_usize(31, 70),  // large
            _ => rng.gen_range_usize(71, 100), // max
        };
        let nc = match n % 5 {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 30),
            3 => rng.gen_range_usize(31, 70),
            _ => rng.gen_range_usize(71, 100),
        };
        let mat = random_binary_matrix(&mut rng, nr, nc);
        emit(mat, &mut out, &mut n);
    }
}
