use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    rows: usize,
    cols: usize,
    values: Vec<i32>,
    mutation_kind: u8,
) -> (result: Vec<Vec<i32>>)
    requires
        1 <= rows <= 6,
        1 <= cols <= 6,
        values.len() == rows * cols,
        forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 9,
    ensures
        1 <= result.len() <= 6,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i].len() <= 6,
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i].len() == result[0].len(),
        forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result[0].len() ==> 1 <= #[trigger] result[i][j] <= 9,
{
    // values is non-empty since rows >= 1 and cols >= 1
    assert(values.len() >= 1) by {
        vstd::arithmetic::mul::lemma_mul_inequality(1, rows as int, cols as int);
    }

    let use_fill: bool = mutation_kind == 1 || mutation_kind == 2
        || mutation_kind == 3 || mutation_kind == 4;
    let fill: i32 = if mutation_kind == 1 {
        1
    } else if mutation_kind == 2 {
        9
    } else if mutation_kind == 3 {
        5
    } else if mutation_kind == 4 {
        values[0]
    } else {
        1
    };

    // Prove fill is in bounds
    assert(1 <= fill <= 9);

    let mut mat: Vec<Vec<i32>> = Vec::new();
    let mut r: usize = 0;
    let mut idx: usize = 0;

    while r < rows
        invariant
            0 <= r <= rows,
            1 <= rows <= 6,
            1 <= cols <= 6,
            mat.len() == r as nat,
            idx == r * cols,
            values.len() == rows * cols,
            1 <= fill <= 9,
            forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 9,
            forall|i: int| 0 <= i < mat.len() ==> (#[trigger] mat[i]).len() == cols,
            forall|i: int, j: int|
                0 <= i < mat.len() && 0 <= j < cols as int
                ==> 1 <= #[trigger] mat[i][j] <= 9,
        decreases rows - r,
    {
        // Prove idx + cols <= values.len()
        assert((r + 1) * cols <= rows * cols) by {
            vstd::arithmetic::mul::lemma_mul_inequality(
                (r + 1) as int, rows as int, cols as int,
            );
        }
        // Distribute: (r+1)*cols == r*cols + cols
        assert((r + 1) * cols == r * cols + cols) by {
            vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(
                cols as int, r as int, 1,
            );
        }
        assert(idx + cols <= values.len());

        let mut row: Vec<i32> = Vec::new();
        let mut c: usize = 0;
        let start_idx: usize = idx;

        while c < cols
            invariant
                0 <= c <= cols,
                1 <= cols <= 6,
                row.len() == c as nat,
                idx == start_idx + c,
                start_idx + cols <= values.len(),
                1 <= fill <= 9,
                forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 9,
                forall|j: int| 0 <= j < c as int ==> 1 <= #[trigger] row[j] <= 9,
            decreases cols - c,
        {
            if use_fill {
                row.push(fill);
            } else {
                row.push(values[idx]);
            }
            idx = idx + 1;
            c = c + 1;
        }

        mat.push(row);

        // Prove idx == (r+1) * cols for the outer invariant after r increments
        assert(idx == start_idx + cols);
        assert(start_idx == r * cols);
        assert((r + 1) * cols == r * cols + cols) by {
            vstd::arithmetic::mul::lemma_mul_is_distributive_add_other_way(
                cols as int, r as int, 1,
            );
        }
        assert(idx == (r + 1) * cols);

        r = r + 1;
    }

    mat
}

} // verus!

extern crate serde_json;
use serde_json::json;

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }

    fn next_u64(&mut self) -> u64 {
        self.0 = self.0
            .wrapping_mul(6364136223846793005)
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

fn random_flat_values(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_range_i64(1, 9) as i32);
    }
    v
}

fn main() {
    use std::collections::HashSet;
    use std::io::Write;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(3044);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!())
        .parent()
        .unwrap()
        .join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |mat: Vec<Vec<i32>>,
                    seen: &mut HashSet<String>,
                    out: &mut std::io::BufWriter<std::fs::File>,
                    count: &mut usize| {
        if *count >= target {
            return;
        }
        let key = format!("{:?}", mat);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::most_frequent_prime(mat.clone());
        writeln!(
            out,
            "{}",
            json!({"input": {"mat": mat}, "output": output})
        )
        .unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<Vec<i32>>> = vec![
        vec![vec![1, 1], vec![9, 9], vec![1, 1]],
        vec![vec![7]],
        vec![vec![9, 7, 8], vec![4, 6, 5], vec![2, 8, 6]],
    ];
    for ex in examples {
        emit(ex, &mut seen, &mut out, &mut count);
    }

    // Structured seeds: various dimensions x mutation kinds
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4];
    let dim_pairs: Vec<(usize, usize)> = vec![
        (1, 1), (1, 6), (6, 1), (6, 6), (2, 3),
        (3, 2), (4, 4), (1, 3), (3, 3), (5, 5),
    ];
    for &(rows, cols) in &dim_pairs {
        for &mk in &mutation_kinds {
            let values = random_flat_values(&mut rng, rows * cols);
            let mat = generate_test_case(rows, cols, values, mk);
            emit(mat, &mut seen, &mut out, &mut count);
        }
    }

    // Random matrices with identity (mk=0)
    for _ in 0..40 {
        let rows = rng.gen_range_usize(1, 6);
        let cols = rng.gen_range_usize(1, 6);
        let values = random_flat_values(&mut rng, rows * cols);
        let mat = generate_test_case(rows, cols, values, 0);
        emit(mat, &mut seen, &mut out, &mut count);
    }

    // Random matrices with random mutation
    while count < target {
        let rows = rng.gen_range_usize(1, 6);
        let cols = rng.gen_range_usize(1, 6);
        let mk = rng.gen_range_usize(0, 4) as u8;
        let values = random_flat_values(&mut rng, rows * cols);
        let mat = generate_test_case(rows, cols, values, mk);
        emit(mat, &mut seen, &mut out, &mut count);
    }
}
