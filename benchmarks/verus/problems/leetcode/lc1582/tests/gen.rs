use vstd::prelude::*;

verus! {

pub fn generate_test_case(mat: Vec<Vec<i32>>, mutation_kind: u8) -> (result: Vec<Vec<i32>>)
    requires
        1 <= mat.len() <= 100,
        forall|r: int| 0 <= r < mat.len() ==> 1 <= #[trigger] mat[r].len() <= 100,
        forall|r: int| 0 <= r < mat.len() ==> #[trigger] mat[r].len() == mat[0].len(),
        forall|r: int, c: int| 0 <= r < mat.len() && 0 <= c < mat[r].len()
            ==> #[trigger] mat[r][c] == 0 || mat[r][c] == 1,
    ensures
        1 <= result.len() <= 100,
        forall|r: int| 0 <= r < result.len() ==> 1 <= #[trigger] result[r].len() <= 100,
        forall|r: int| 0 <= r < result.len() ==> #[trigger] result[r].len() == result[0].len(),
        forall|r: int, c: int| 0 <= r < result.len() && 0 <= c < result[r].len()
            ==> #[trigger] result[r][c] == 0 || result[r][c] == 1,
{
    if mutation_kind == 0 {
        // identity
        mat
    } else if mutation_kind == 1 {
        // set all cells to 0
        let n_cols = mat[0].len();
        let mut m = mat;
        let mut i: usize = 0;
        while i < m.len()
            invariant
                m.len() == mat.len(),
                1 <= m.len() <= 100,
                n_cols == mat[0].len(),
                forall|r: int| 0 <= r < m.len() ==> #[trigger] m[r].len() == n_cols,
                1 <= n_cols <= 100,
                forall|r: int| 0 <= r < i ==>
                    forall|c: int| 0 <= c < #[trigger] m[r].len() ==> #[trigger] m[r][c] == 0,
                forall|r: int| i <= r < m.len() ==>
                    forall|c: int| 0 <= c < #[trigger] m[r].len()
                        ==> #[trigger] m[r][c] == 0 || m[r][c] == 1,
            decreases m.len() - i,
        {
            let mut row = Vec::new();
            let mut j: usize = 0;
            while j < n_cols
                invariant
                    0 <= j <= n_cols,
                    row.len() == j,
                    forall|k: int| 0 <= k < j ==> #[trigger] row[k] == 0,
                decreases n_cols - j,
            {
                row.push(0i32);
                j += 1;
            }
            m.set(i, row);
            i += 1;
        }
        m
    } else if mutation_kind == 2 {
        // flip cell (0,0)
        let mut m = mat;
        let mut row0 = m[0].clone();
        let val = if row0[0] == 0 { 1i32 } else { 0i32 };
        row0.set(0, val);
        m.set(0, row0);
        m
    } else if mutation_kind == 3 {
        // set first row to all zeros
        let n_cols = mat[0].len();
        let mut m = mat;
        let mut row0 = Vec::new();
        let mut j: usize = 0;
        while j < n_cols
            invariant
                0 <= j <= n_cols,
                row0.len() == j,
                forall|k: int| 0 <= k < j ==> #[trigger] row0[k] == 0,
            decreases n_cols - j,
        {
            row0.push(0i32);
            j += 1;
        }
        m.set(0, row0);
        m
    } else if mutation_kind == 4 {
        // set first row to all zeros then put a 1 at (0,0) — potential special position
        let n_cols = mat[0].len();
        let mut m = mat;
        let mut row0 = Vec::new();
        let mut j: usize = 0;
        while j < n_cols
            invariant
                0 <= j <= n_cols,
                row0.len() == j,
                forall|k: int| 0 <= k < j ==> #[trigger] row0[k] == 0,
            decreases n_cols - j,
        {
            row0.push(0i32);
            j += 1;
        }
        row0.set(0, 1i32);
        m.set(0, row0);
        m
    } else if mutation_kind == 5 {
        // set all cells to 1
        let n_cols = mat[0].len();
        let mut m = mat;
        let mut i: usize = 0;
        while i < m.len()
            invariant
                m.len() == mat.len(),
                1 <= m.len() <= 100,
                n_cols == mat[0].len(),
                forall|r: int| 0 <= r < m.len() ==> #[trigger] m[r].len() == n_cols,
                1 <= n_cols <= 100,
                forall|r: int| 0 <= r < i ==>
                    forall|c: int| 0 <= c < #[trigger] m[r].len() ==> #[trigger] m[r][c] == 1,
                forall|r: int| i <= r < m.len() ==>
                    forall|c: int| 0 <= c < #[trigger] m[r].len()
                        ==> #[trigger] m[r][c] == 0 || m[r][c] == 1,
            decreases m.len() - i,
        {
            let mut row = Vec::new();
            let mut j: usize = 0;
            while j < n_cols
                invariant
                    0 <= j <= n_cols,
                    row.len() == j,
                    forall|k: int| 0 <= k < j ==> #[trigger] row[k] == 1,
                decreases n_cols - j,
            {
                row.push(1i32);
                j += 1;
            }
            m.set(i, row);
            i += 1;
        }
        m
    } else if mutation_kind == 6 {
        // create identity-like matrix: set diagonal to 1, rest to 0
        // (produces max special positions when square)
        let n_cols = mat[0].len();
        let mut m = mat;
        let mut i: usize = 0;
        while i < m.len()
            invariant
                m.len() == mat.len(),
                1 <= m.len() <= 100,
                n_cols == mat[0].len(),
                forall|r: int| 0 <= r < m.len() ==> #[trigger] m[r].len() == n_cols,
                1 <= n_cols <= 100,
                forall|r: int| 0 <= r < i ==>
                    forall|c: int| 0 <= c < #[trigger] m[r].len()
                        ==> #[trigger] m[r][c] == 0 || m[r][c] == 1,
                forall|r: int| i <= r < m.len() ==>
                    forall|c: int| 0 <= c < #[trigger] m[r].len()
                        ==> #[trigger] m[r][c] == 0 || m[r][c] == 1,
            decreases m.len() - i,
        {
            let mut row = Vec::new();
            let mut j: usize = 0;
            while j < n_cols
                invariant
                    0 <= j <= n_cols,
                    row.len() == j,
                    forall|k: int| 0 <= k < j ==> #[trigger] row[k] == 0 || row[k] == 1,
                decreases n_cols - j,
            {
                if j == i {
                    row.push(1i32);
                } else {
                    row.push(0i32);
                }
                j += 1;
            }
            m.set(i, row);
            i += 1;
        }
        m
    } else {
        // fallback: identity
        mat
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

fn mutate(mat: Vec<Vec<i32>>, mutation_kind: u8) -> Vec<Vec<i32>> {
    generate_test_case(mat, mutation_kind)
}

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

fn sparse_binary_matrix(rng: &mut Rng, rows: usize, cols: usize) -> Vec<Vec<i32>> {
    // Mostly zeros with a few ones — more likely to have special positions
    let mut mat = vec![vec![0i32; cols]; rows];
    let num_ones = rng.gen_range_usize(1, rows.min(cols).max(1));
    for _ in 0..num_ones {
        let r = rng.gen_range_usize(0, rows - 1);
        let c = rng.gen_range_usize(0, cols - 1);
        mat[r][c] = 1;
    }
    mat
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1582);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |mat: Vec<Vec<i32>>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target {
            return;
        }
        let key = format!("{:?}", mat);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::num_special(mat.clone());
        writeln!(out, "{}", json!({"input": {"mat": mat}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<Vec<i32>>> = vec![
        vec![vec![1,0,0], vec![0,0,1], vec![1,0,0]],
        vec![vec![1,0,0], vec![0,1,0], vec![0,0,1]],
    ];

    // Curated seeds
    let seeds: Vec<Vec<Vec<i32>>> = vec![
        vec![vec![0]],
        vec![vec![1]],
        vec![vec![0, 0], vec![0, 0]],
        vec![vec![1, 0], vec![0, 1]],
        vec![vec![1, 1], vec![1, 1]],
        vec![vec![0, 1, 0], vec![0, 0, 0], vec![0, 1, 0]],
        vec![vec![1, 0, 0, 0], vec![0, 1, 0, 0], vec![0, 0, 1, 0]],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6];

    // Emit examples with identity mutation
    for ex in &examples {
        emit(ex.clone(), &mut seen, &mut out, &mut count);
    }

    // Apply every mutation to curated seeds
    for s in &seeds {
        for &mk in &mutation_kinds {
            let result = mutate(s.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random matrices with random mutations across size classes
    while count < target {
        let (rows, cols) = match count % 5 {
            0 => (rng.gen_range_usize(1, 3), rng.gen_range_usize(1, 3)),       // tiny
            1 => (rng.gen_range_usize(1, 10), rng.gen_range_usize(1, 10)),      // small
            2 => (rng.gen_range_usize(5, 30), rng.gen_range_usize(5, 30)),      // medium
            3 => (rng.gen_range_usize(20, 60), rng.gen_range_usize(20, 60)),    // large
            _ => (rng.gen_range_usize(50, 100), rng.gen_range_usize(50, 100)),  // max
        };
        let mk = rng.gen_range_usize(0, 6) as u8;
        let base = if count % 3 == 0 {
            sparse_binary_matrix(&mut rng, rows, cols)
        } else {
            random_binary_matrix(&mut rng, rows, cols)
        };
        let result = mutate(base, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }
}
