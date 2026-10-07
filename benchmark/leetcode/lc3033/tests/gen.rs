use vstd::prelude::*;

verus! {

/// True when column j has at least one non-negative element in rows [0..k)
pub open spec fn col_has_nonneg(matrix: Seq<Vec<i32>>, j: int, k: int) -> bool
    decreases k,
{
    if k <= 0 {
        false
    } else if matrix[k - 1][j] >= 0 {
        true
    } else {
        col_has_nonneg(matrix, j, k - 1)
    }
}

proof fn lemma_col_has_nonneg_witness(matrix: Seq<Vec<i32>>, j: int, k: int, w: int)
    requires
        0 <= w < k,
        k <= matrix.len(),
        0 <= j < matrix[w].len(),
        matrix[w][j] >= 0,
    ensures
        col_has_nonneg(matrix, j, k),
    decreases k,
{
    if k <= 0 {
    } else if matrix[k - 1][j] >= 0 {
    } else {
        lemma_col_has_nonneg_witness(matrix, j, k - 1, w);
    }
}

pub fn generate_test_case(
    m: usize,
    n: usize,
    nonneg_vals: Vec<i32>,
    other_val: i32,
    mutation_kind: u8,
) -> (matrix: Vec<Vec<i32>>)
    requires
        2 <= m <= 50,
        2 <= n <= 50,
        nonneg_vals.len() == n,
        forall|k: int| 0 <= k < nonneg_vals.len() ==> 0 <= #[trigger] nonneg_vals[k] <= 100,
        -1 <= other_val <= 100,
    ensures
        2 <= matrix.len() <= 50,
        2 <= matrix[0].len() <= 50,
        forall |i: int| 0 <= i < matrix.len() ==> #[trigger] matrix[i].len() == matrix[0].len(),
        forall |i: int, j: int|
            0 <= i < matrix.len() && 0 <= j < matrix[i].len()
            ==> -1 <= #[trigger] matrix[i][j] <= 100,
        forall |j: int| 0 <= j < matrix[0].len()
            ==> #[trigger] col_has_nonneg(matrix@, j, matrix.len() as int),
{
    // Determine effective fill value based on mutation
    let fill: i32 = if mutation_kind == 1 {
        -1i32    // force all other cells to -1
    } else if mutation_kind == 4 {
        0i32     // force other cells to 0
    } else if mutation_kind == 5 {
        100i32   // force other cells to 100
    } else {
        other_val
    };

    let mut matrix: Vec<Vec<i32>> = Vec::new();

    // Build first row based on mutation
    if mutation_kind == 2 {
        // Force first row to all 0
        let mut row0: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                j <= n,
                row0.len() == j,
                forall|c: int| 0 <= c < j ==> row0[c] == 0i32,
            decreases n - j,
        {
            row0.push(0i32);
            j += 1;
        }
        matrix.push(row0);
    } else if mutation_kind == 3 {
        // Force first row to all 100
        let mut row0: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                j <= n,
                row0.len() == j,
                forall|c: int| 0 <= c < j ==> row0[c] == 100i32,
            decreases n - j,
        {
            row0.push(100i32);
            j += 1;
        }
        matrix.push(row0);
    } else {
        // Use nonneg_vals directly
        matrix.push(nonneg_vals);
    }

    assert(matrix.len() == 1);
    assert(matrix[0].len() == n);

    // Build remaining rows filled with `fill`
    let mut i: usize = 1;
    while i < m
        invariant
            1 <= i <= m,
            matrix.len() == i,
            matrix[0].len() == n,
            forall|r: int| 0 <= r < i ==> #[trigger] matrix[r].len() == n,
            forall|r: int, c: int|
                0 <= r < i && 0 <= c < n
                ==> -1 <= #[trigger] matrix[r][c] <= 100,
            forall|c: int| 0 <= c < n ==> matrix[0][c] >= 0,
            -1 <= fill <= 100,
            2 <= m <= 50,
            2 <= n <= 50,
        decreases m - i,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                j <= n,
                row.len() == j,
                forall|c: int| 0 <= c < j ==> -1 <= #[trigger] row[c] <= 100,
                -1 <= fill <= 100,
            decreases n - j,
        {
            row.push(fill);
            j += 1;
        }
        assert(row.len() == n);
        matrix.push(row);
        i += 1;
    }

    // Prove col_has_nonneg for each column using row 0 as witness
    proof {
        assert forall|j: int| 0 <= j < matrix[0].len() implies
            #[trigger] col_has_nonneg(matrix@, j, matrix.len() as int)
        by {
            lemma_col_has_nonneg_witness(matrix@, j, matrix.len() as int, 0);
        }
    }

    matrix
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

fn random_nonneg_row(rng: &mut Rng, n: usize) -> Vec<i32> {
    (0..n).map(|_| rng.gen_range_i64(0, 100) as i32).collect()
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(3033);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5];

    let mut emit = |matrix: Vec<Vec<i32>>,
                    seen: &mut HashSet<String>,
                    out: &mut std::io::BufWriter<std::fs::File>,
                    count: &mut usize| {
        if *count >= target {
            return;
        }
        let key = format!("{:?}", matrix);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::modified_matrix(matrix.clone());
        writeln!(
            out,
            "{}",
            json!({"input": {"matrix": matrix}, "output": output})
        )
        .unwrap();
        *count += 1;
    };

    // Hand-crafted examples from the problem description
    let example1 = vec![vec![1, 2, -1], vec![4, -1, 6], vec![7, 8, 9]];
    let example2 = vec![vec![3, -1], vec![5, 2]];
    emit(example1, &mut seen, &mut out, &mut count);
    emit(example2, &mut seen, &mut out, &mut count);

    // Systematic: vary dimensions and mutations
    let dims: Vec<(usize, usize)> = vec![
        (2, 2),
        (2, 3),
        (3, 2),
        (3, 3),
        (5, 5),
        (10, 10),
        (2, 50),
        (50, 2),
        (50, 50),
    ];

    for &(m, n) in &dims {
        for &mk in &mutation_kinds {
            if count >= target {
                break;
            }
            let nonneg_vals = random_nonneg_row(&mut rng, n);
            let other_val = rng.gen_range_i64(-1, 100) as i32;
            let matrix = generate_test_case(m, n, nonneg_vals, other_val, mk);
            emit(matrix, &mut seen, &mut out, &mut count);
        }
    }

    // Random diverse cases with size classes
    while count < target {
        let m = match rng.gen_range_usize(0, 4) {
            0 => 2,                               // minimum
            1 => rng.gen_range_usize(2, 5),        // tiny
            2 => rng.gen_range_usize(5, 15),       // small
            3 => rng.gen_range_usize(15, 35),      // medium
            _ => rng.gen_range_usize(35, 50),      // large
        };
        let n = match rng.gen_range_usize(0, 4) {
            0 => 2,                                // minimum
            1 => rng.gen_range_usize(2, 5),        // tiny
            2 => rng.gen_range_usize(5, 15),       // small
            3 => rng.gen_range_usize(15, 35),      // medium
            _ => rng.gen_range_usize(35, 50),      // large
        };

        // Mix boundary values into the non-negative row (~20%)
        let nonneg_vals: Vec<i32> = (0..n)
            .map(|_| {
                if rng.gen_range_usize(0, 4) == 0 {
                    [0i32, 100, 1, 50][rng.gen_range_usize(0, 3)]
                } else {
                    rng.gen_range_i64(0, 100) as i32
                }
            })
            .collect();

        // Frequently test -1 as fill value
        let other_val = if rng.gen_range_usize(0, 3) == 0 {
            -1i32
        } else {
            rng.gen_range_i64(-1, 100) as i32
        };

        let mk = mutation_kinds[rng.gen_range_usize(0, mutation_kinds.len() - 1)];
        let matrix = generate_test_case(m, n, nonneg_vals, other_val, mk);
        emit(matrix, &mut seen, &mut out, &mut count);
    }
}
