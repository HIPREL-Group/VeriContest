use vstd::prelude::*;

verus! {

pub fn generate_test_case(matrix: &mut Vec<Vec<i32>>, mutation_kind: u8)
    requires
        1 <= (*old(matrix)).len() <= 200,
        1 <= (*old(matrix))[0].len() <= 200,
        forall |row: int| 0 <= row < (*old(matrix)).len() ==> #[trigger] (*old(matrix))[row].len() == (*old(matrix))[0].len(),
        forall |row: int, col: int|
            0 <= row < (*old(matrix)).len() && 0 <= col < (*old(matrix))[row].len() ==> i32::MIN <= #[trigger] (*old(matrix))[row][col] <= i32::MAX,
    ensures
        1 <= (*old(matrix)).len() <= 200,
        1 <= (*old(matrix))[0].len() <= 200,
        forall |row: int| 0 <= row < (*old(matrix)).len() ==> #[trigger] (*old(matrix))[row].len() == (*old(matrix))[0].len(),
        forall |row: int, col: int|
            0 <= row < (*old(matrix)).len() && 0 <= col < (*old(matrix))[row].len() ==> i32::MIN <= #[trigger] (*old(matrix))[row][col] <= i32::MAX,
{
    let rows = matrix.len();
    let cols = matrix[0].len();

    if mutation_kind == 1 {
        // Set element [0][0] to 0 (corner zero)
        let mut row0 = matrix[0].clone();
        row0.set(0, 0i32);
        matrix.set(0, row0);
    } else if mutation_kind == 2 && rows > 1 && cols > 1 {
        // Set element [rows-1][cols-1] to 0 (opposite corner)
        let last_r = rows - 1;
        let last_c = cols - 1;
        let mut row_last = matrix[last_r].clone();
        row_last.set(last_c, 0i32);
        matrix.set(last_r, row_last);
    } else if mutation_kind == 3 {
        // Set first row to all zeros
        let mut row0 = matrix[0].clone();
        let mut c: usize = 0;
        while c < cols
            invariant
                0 <= c <= cols,
                row0.len() == cols,
            decreases cols - c,
        {
            row0.set(c, 0i32);
            c += 1;
        }
        matrix.set(0, row0);
    } else if mutation_kind == 4 {
        // Set first column to all zeros
        let mut r: usize = 0;
        while r < rows
            invariant
                0 <= r <= rows,
                1 <= cols,
                matrix.len() == rows,
                forall |i: int| 0 <= i < matrix.len() ==> (#[trigger] matrix[i]).len() == cols,
            decreases rows - r,
        {
            let mut row_r = matrix[r].clone();
            row_r.set(0, 0i32);
            matrix.set(r, row_r);
            r += 1;
        }
    } else if mutation_kind == 5 {
        // Set center element to 0
        let mid_r = rows / 2;
        let mid_c = cols / 2;
        let mut row_mid = matrix[mid_r].clone();
        row_mid.set(mid_c, 0i32);
        matrix.set(mid_r, row_mid);
    } else if mutation_kind == 6 {
        // Set all elements to 0
        let mut r: usize = 0;
        while r < rows
            invariant
                0 <= r <= rows,
                1 <= cols,
                matrix.len() == rows,
                forall |i: int| 0 <= i < matrix.len() ==> (#[trigger] matrix[i]).len() == cols,
            decreases rows - r,
        {
            let mut row_r = matrix[r].clone();
            let mut c: usize = 0;
            while c < cols
                invariant
                    0 <= c <= cols,
                    row_r.len() == cols,
                decreases cols - c,
            {
                row_r.set(c, 0i32);
                c += 1;
            }
            matrix.set(r, row_r);
            r += 1;
        }
    }
    // mutation_kind == 0 or fallback: identity (no mutation)
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

fn build_matrix(rng: &mut Rng, m: usize, n: usize, lo: i32, hi: i32) -> Vec<Vec<i32>> {
    let mut matrix = Vec::with_capacity(m);
    for _ in 0..m {
        let mut row = Vec::with_capacity(n);
        for _ in 0..n {
            row.push(rng.gen_range_i64(lo as i64, hi as i64) as i32);
        }
        matrix.push(row);
    }
    matrix
}

fn build_uniform_matrix(m: usize, n: usize, val: i32) -> Vec<Vec<i32>> {
    let mut matrix = Vec::with_capacity(m);
    for _ in 0..m {
        matrix.push(vec![val; n]);
    }
    matrix
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(73);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |matrix: Vec<Vec<i32>>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count {
            return;
        }
        let key = format!("{:?}", matrix);
        if !seen.insert(key) {
            return;
        }
        let mut mat_clone = matrix.clone();
        Solution::set_zeroes(&mut mat_clone);
        writeln!(out, "{}", json!({
            "input": {"matrix": matrix},
            "output": mat_clone
        })).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    emit(vec![vec![1,1,1], vec![1,0,1], vec![1,1,1]], &mut seen, &mut out, &mut count);
    emit(vec![vec![0,1,2,0], vec![3,4,5,2], vec![1,3,1,5]], &mut seen, &mut out, &mut count);

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6];

    // Seed matrices with diverse shapes and values
    let seed_matrices: Vec<Vec<Vec<i32>>> = vec![
        vec![vec![1]],
        vec![vec![0]],
        vec![vec![1, 2], vec![3, 4]],
        vec![vec![1, 0], vec![0, 1]],
        vec![vec![1, 2, 3], vec![4, 5, 6], vec![7, 8, 9]],
        vec![vec![1, 2, 3, 4]],
        vec![vec![1], vec![2], vec![3], vec![4]],
        build_uniform_matrix(5, 5, 1),
        build_uniform_matrix(3, 3, i32::MAX),
        build_uniform_matrix(3, 3, i32::MIN),
        build_uniform_matrix(3, 3, 0),
        vec![vec![-1, -2, -3], vec![-4, 0, -6], vec![-7, -8, -9]],
    ];

    for seed_mat in &seed_matrices {
        for &mk in &mutation_kinds {
            let mut mat = seed_mat.clone();
            generate_test_case(&mut mat, mk);
            emit(mat, &mut seen, &mut out, &mut count);
        }
    }

    // Random test cases with diverse size classes
    while count < target_count {
        let (m, n) = match count % 5 {
            0 => (rng.gen_range_usize(1, 3), rng.gen_range_usize(1, 3)),
            1 => (rng.gen_range_usize(1, 10), rng.gen_range_usize(1, 10)),
            2 => (rng.gen_range_usize(11, 50), rng.gen_range_usize(11, 50)),
            3 => (rng.gen_range_usize(51, 150), rng.gen_range_usize(51, 150)),
            _ => (rng.gen_range_usize(151, 200), rng.gen_range_usize(151, 200)),
        };

        let (lo, hi): (i32, i32) = if count % 5 == 0 {
            match rng.gen_range_usize(0, 4) {
                0 => (i32::MIN, i32::MIN + 100),
                1 => (i32::MAX - 100, i32::MAX),
                2 => (-1, 1),
                3 => (0, 0),
                _ => (-1000, 1000),
            }
        } else {
            (-1_000_000, 1_000_000)
        };

        let mut matrix = build_matrix(&mut rng, m, n, lo, hi);

        // Sprinkle 0-3 zeros at random positions
        let num_zeros = rng.gen_range_usize(0, 3);
        for _ in 0..num_zeros {
            let zr = rng.gen_range_usize(0, m - 1);
            let zc = rng.gen_range_usize(0, n - 1);
            matrix[zr][zc] = 0;
        }

        let mk = rng.gen_range_usize(0, 6) as u8;
        generate_test_case(&mut matrix, mk);
        emit(matrix, &mut seen, &mut out, &mut count);
    }
}
