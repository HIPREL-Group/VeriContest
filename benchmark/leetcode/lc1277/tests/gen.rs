use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    matrix: Vec<Vec<i32>>,
    mutation_kind: u8,
) -> (result: Vec<Vec<i32>>)
    requires
        1 <= matrix.len() <= 300,
        forall |i: int| 0 <= i < matrix.len() ==> 1 <= (#[trigger] matrix[i]).len() <= 300,
        forall |i: int| 0 <= i < matrix.len() ==> (#[trigger] matrix[i]).len() == matrix[0].len(),
        forall |i: int, j: int| 0 <= i < matrix.len() && 0 <= j < matrix[0].len()
            ==> #[trigger] matrix[i][j] == 0 || matrix[i][j] == 1,
    ensures
        1 <= result.len() <= 300,
        forall |i: int| 0 <= i < result.len() ==> 1 <= (#[trigger] result[i]).len() <= 300,
        forall |i: int| 0 <= i < result.len() ==> (#[trigger] result[i]).len() == result[0].len(),
        forall |i: int, j: int| 0 <= i < result.len() && 0 <= j < result[0].len()
            ==> #[trigger] result[i][j] == 0 || result[i][j] == 1,
{
    if mutation_kind == 0 {
        // identity
        matrix
    } else if mutation_kind == 1 || mutation_kind == 2 {
        // construct all-1s (mutation 1) or all-0s (mutation 2) matrix of same dimensions
        let fill: i32 = if mutation_kind == 1 { 1 } else { 0 };
        let rows = matrix.len();
        let cols = matrix[0].len();
        let mut res: Vec<Vec<i32>> = Vec::new();
        let mut i: usize = 0;
        while i < rows
            invariant
                0 <= i <= rows,
                1 <= rows <= 300,
                1 <= cols <= 300,
                fill == 0 || fill == 1,
                res.len() == i as nat,
                forall|r: int| 0 <= r < i as int ==> (#[trigger] res[r]).len() == cols,
                forall|r: int, c: int| 0 <= r < i as int && 0 <= c < cols as int
                    ==> #[trigger] res[r][c] == 0 || res[r][c] == 1,
            decreases rows - i,
        {
            let mut row: Vec<i32> = Vec::new();
            let mut j: usize = 0;
            while j < cols
                invariant
                    0 <= j <= cols,
                    1 <= cols <= 300,
                    fill == 0 || fill == 1,
                    row.len() == j as nat,
                    forall|c: int| 0 <= c < j as int ==> (#[trigger] row[c] == 0 || row[c] == 1),
                decreases cols - j,
            {
                row.push(fill);
                j += 1;
            }
            res.push(row);
            i += 1;
        }
        res
    } else {
        // fallback: identity
        matrix
    }
}

} // verus!

extern crate serde_json;
use serde_json::json;

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let (lo, hi) = if lo <= hi { (lo, hi) } else { (hi, lo) };
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

struct Solution;
include!("../code.rs");

fn random_binary_matrix(rng: &mut Rng, m: usize, n: usize) -> Vec<Vec<i32>> {
    let mut mat = Vec::with_capacity(m);
    for _ in 0..m {
        let mut row = Vec::with_capacity(n);
        for _ in 0..n {
            row.push(rng.gen_range_usize(0, 1) as i32);
        }
        mat.push(row);
    }
    mat
}

fn all_val_matrix(m: usize, n: usize, val: i32) -> Vec<Vec<i32>> {
    let mut mat = Vec::with_capacity(m);
    for _ in 0..m {
        mat.push(vec![val; n]);
    }
    mat
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1277);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |mat: Vec<Vec<i32>>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count { return; }
        let key = format!("{:?}", mat);
        if !seen.insert(key) { return; }
        let output = Solution::count_squares(mat.clone());
        writeln!(out, "{}", json!({"input": {"matrix": mat}, "output": output})).unwrap();
        *count += 1;
    };

    // Example test cases from description.md
    let ex1 = vec![vec![0,1,1,1], vec![1,1,1,1], vec![0,1,1,1]];
    let ex2 = vec![vec![1,0,1], vec![1,1,0], vec![1,1,0]];
    emit(ex1, &mut seen, &mut out, &mut count);
    emit(ex2, &mut seen, &mut out, &mut count);

    // Structured seed matrices with all mutation kinds
    let seed_matrices: Vec<Vec<Vec<i32>>> = vec![
        // 1x1
        vec![vec![0]],
        vec![vec![1]],
        // 1xN
        vec![vec![1, 1, 1, 1, 1]],
        vec![vec![0, 0, 0, 0, 0]],
        vec![vec![1, 0, 1, 0, 1]],
        // Mx1
        vec![vec![1], vec![1], vec![1]],
        vec![vec![0], vec![1], vec![0]],
        // Small squares
        vec![vec![1, 1], vec![1, 1]],
        vec![vec![0, 0], vec![0, 0]],
        vec![vec![1, 0], vec![0, 1]],
        // 3x3 patterns
        all_val_matrix(3, 3, 1),
        all_val_matrix(3, 3, 0),
        vec![vec![1, 1, 0], vec![1, 1, 0], vec![0, 0, 0]],
        // Rectangular
        vec![vec![1, 1, 1, 1], vec![1, 1, 1, 1]],
        vec![vec![1, 1], vec![1, 1], vec![1, 1], vec![1, 1]],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2];

    for mat in &seed_matrices {
        for &mk in &mutation_kinds {
            let result = generate_test_case(mat.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random matrices across size classes
    let mut _attempts_0 = 0usize;
    while count < target_count {
        _attempts_0 += 1; if _attempts_0 > 10000 { break; }
        let (m, n) = match count % 7 {
            0 => (1, 1),                                                      // 1x1
            1 => (rng.gen_range_usize(1, 3), rng.gen_range_usize(1, 3)),      // tiny
            2 => (rng.gen_range_usize(2, 10), rng.gen_range_usize(2, 10)),    // small
            3 => (rng.gen_range_usize(5, 30), rng.gen_range_usize(5, 30)),    // medium
            4 => (rng.gen_range_usize(10, 50), rng.gen_range_usize(10, 50)),  // large
            5 => (rng.gen_range_usize(50, 150), rng.gen_range_usize(50, 150)),// bigger
            _ => (rng.gen_range_usize(100, 300), rng.gen_range_usize(100, 300)), // max
        };

        let mat = if count % 10 == 0 {
            all_val_matrix(m, n, 1)
        } else if count % 10 == 5 {
            all_val_matrix(m, n, 0)
        } else {
            random_binary_matrix(&mut rng, m, n)
        };

        let mk = rng.gen_range_usize(0, 2) as u8;
        let result = generate_test_case(mat, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }
}
