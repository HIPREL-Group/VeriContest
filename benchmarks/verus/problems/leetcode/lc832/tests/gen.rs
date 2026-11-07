use vstd::prelude::*;

verus! {

/// Helper: build a row of n binary values from flat data starting at cursor.
fn build_row_from_flat(flat: &Vec<i32>, cursor: usize, n: usize) -> (row: Vec<i32>)
    requires
        cursor + n <= flat.len(),
        forall|k: int| 0 <= k < flat.len() ==> 0 <= #[trigger] flat[k] <= 1,
    ensures
        row.len() == n,
        forall|c: int| 0 <= c < row.len() ==> 0 <= #[trigger] row[c] <= 1,
{
    let mut row: Vec<i32> = Vec::new();
    let mut j: usize = 0;
    while j < n
        invariant
            0 <= j <= n,
            cursor + n <= flat.len(),
            row.len() == j,
            forall|k: int| 0 <= k < flat.len() ==> 0 <= #[trigger] flat[k] <= 1,
            forall|c: int| 0 <= c < j ==> 0 <= #[trigger] row[c] <= 1,
        decreases n - j,
    {
        row.push(flat[cursor + j]);
        j += 1;
    }
    row
}

/// Helper: build a row of n copies of a constant binary value.
fn build_constant_row(val: i32, n: usize) -> (row: Vec<i32>)
    requires
        0 <= val <= 1,
    ensures
        row.len() == n,
        forall|c: int| 0 <= c < row.len() ==> 0 <= #[trigger] row[c] <= 1,
{
    let mut row: Vec<i32> = Vec::new();
    let mut j: usize = 0;
    while j < n
        invariant
            0 <= j <= n,
            0 <= val <= 1,
            row.len() == j,
            forall|c: int| 0 <= c < j ==> 0 <= #[trigger] row[c] <= 1,
        decreases n - j,
    {
        row.push(val);
        j += 1;
    }
    row
}

/// Generate a valid n×n binary matrix.
///
/// Construction parameters:
///   - `n`: side length (1..=20)
///   - `flat`: flat array of binary values, length >= n*n
///   - `mutation_kind`: selects a mutation strategy
///
/// The ensures match exactly the requires from spec.rs.
pub fn generate_test_case(n: usize, flat: Vec<i32>, mutation_kind: u8) -> (image: Vec<Vec<i32>>)
    requires
        1 <= n <= 20,
        flat.len() >= n * n,
        forall|k: int| 0 <= k < flat.len() ==> 0 <= #[trigger] flat[k] <= 1,
    ensures
        1 <= image.len() <= 20,
        forall|i: int| 0 <= i < image.len() ==> #[trigger] image[i].len() == image.len(),
        forall|i: int, j: int| 0 <= i < image.len() && 0 <= j < image[i].len() ==> 0 <= #[trigger] image[i][j] <= 1,
{
    if mutation_kind == 0 {
        // Build n×n matrix from flat data
        let mut image: Vec<Vec<i32>> = Vec::new();
        let mut i: usize = 0;
        let mut cursor: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                1 <= n <= 20,
                cursor == i * n,
                cursor <= flat.len(),
                flat.len() >= n * n,
                image.len() == i,
                forall|k: int| 0 <= k < flat.len() ==> 0 <= #[trigger] flat[k] <= 1,
                forall|r: int| 0 <= r < i ==> #[trigger] image[r].len() == n,
                forall|r: int, c: int| 0 <= r < i && 0 <= c < image[r].len() ==> 0 <= #[trigger] image[r][c] <= 1,
            decreases n - i,
        {
            assert(cursor + n <= flat.len()) by {
                assert((i as int + 1) * (n as int) <= (n as int) * (n as int)) by(nonlinear_arith)
                    requires i < n, n >= 1;
                assert(cursor as int + n as int == (i as int + 1) * (n as int)) by(nonlinear_arith)
                    requires cursor as int == i as int * n as int, n >= 1;
            };
            let row = build_row_from_flat(&flat, cursor, n);
            image.push(row);
            assert(cursor + n == (i + 1) * n) by {
                assert(cursor as int + n as int == (i as int + 1) * (n as int)) by(nonlinear_arith)
                    requires cursor as int == i as int * n as int, n >= 1;
            };
            cursor = cursor + n;
            i += 1;
        }
        image
    } else if mutation_kind == 1 {
        // All zeros matrix
        let mut image: Vec<Vec<i32>> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                1 <= n <= 20,
                image.len() == i,
                forall|r: int| 0 <= r < i ==> #[trigger] image[r].len() == n,
                forall|r: int, c: int| 0 <= r < i && 0 <= c < image[r].len() ==> 0 <= #[trigger] image[r][c] <= 1,
            decreases n - i,
        {
            let row = build_constant_row(0, n);
            image.push(row);
            i += 1;
        }
        image
    } else if mutation_kind == 2 {
        // All ones matrix
        let mut image: Vec<Vec<i32>> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                1 <= n <= 20,
                image.len() == i,
                forall|r: int| 0 <= r < i ==> #[trigger] image[r].len() == n,
                forall|r: int, c: int| 0 <= r < i && 0 <= c < image[r].len() ==> 0 <= #[trigger] image[r][c] <= 1,
            decreases n - i,
        {
            let row = build_constant_row(1, n);
            image.push(row);
            i += 1;
        }
        image
    } else if mutation_kind == 3 {
        // Identity matrix (diagonal = 1, rest = 0)
        let mut image: Vec<Vec<i32>> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                1 <= n <= 20,
                image.len() == i,
                forall|r: int| 0 <= r < i ==> #[trigger] image[r].len() == n,
                forall|r: int, c: int| 0 <= r < i && 0 <= c < image[r].len() ==> 0 <= #[trigger] image[r][c] <= 1,
            decreases n - i,
        {
            let mut row: Vec<i32> = Vec::new();
            let mut j: usize = 0;
            while j < n
                invariant
                    0 <= j <= n,
                    row.len() == j,
                    forall|c: int| 0 <= c < j ==> 0 <= #[trigger] row[c] <= 1,
                decreases n - j,
            {
                if j == i { row.push(1); } else { row.push(0); }
                j += 1;
            }
            image.push(row);
            i += 1;
        }
        image
    } else if mutation_kind == 4 {
        // Checkerboard: alternate 0/1 using parity tracking
        let mut image: Vec<Vec<i32>> = Vec::new();
        let mut i: usize = 0;
        let mut parity: i32 = 0;
        while i < n
            invariant
                0 <= i <= n,
                1 <= n <= 20,
                0 <= parity <= 1,
                image.len() == i,
                forall|r: int| 0 <= r < i ==> #[trigger] image[r].len() == n,
                forall|r: int, c: int| 0 <= r < i && 0 <= c < image[r].len() ==> 0 <= #[trigger] image[r][c] <= 1,
            decreases n - i,
        {
            let mut row: Vec<i32> = Vec::new();
            let mut j: usize = 0;
            let mut cell: i32 = parity;
            while j < n
                invariant
                    0 <= j <= n,
                    0 <= cell <= 1,
                    row.len() == j,
                    forall|c: int| 0 <= c < j ==> 0 <= #[trigger] row[c] <= 1,
                decreases n - j,
            {
                row.push(cell);
                cell = 1 - cell;
                j += 1;
            }
            image.push(row);
            parity = 1 - parity;
            i += 1;
        }
        image
    } else {
        // Fallback: build from flat data (same as mutation_kind 0)
        let mut image: Vec<Vec<i32>> = Vec::new();
        let mut i: usize = 0;
        let mut cursor: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                1 <= n <= 20,
                cursor == i * n,
                cursor <= flat.len(),
                flat.len() >= n * n,
                image.len() == i,
                forall|k: int| 0 <= k < flat.len() ==> 0 <= #[trigger] flat[k] <= 1,
                forall|r: int| 0 <= r < i ==> #[trigger] image[r].len() == n,
                forall|r: int, c: int| 0 <= r < i && 0 <= c < image[r].len() ==> 0 <= #[trigger] image[r][c] <= 1,
            decreases n - i,
        {
            assert(cursor + n <= flat.len()) by {
                assert((i as int + 1) * (n as int) <= (n as int) * (n as int)) by(nonlinear_arith)
                    requires i < n, n >= 1;
                assert(cursor as int + n as int == (i as int + 1) * (n as int)) by(nonlinear_arith)
                    requires cursor as int == i as int * n as int, n >= 1;
            };
            let row = build_row_from_flat(&flat, cursor, n);
            image.push(row);
            assert(cursor + n == (i + 1) * n) by {
                assert(cursor as int + n as int == (i as int + 1) * (n as int)) by(nonlinear_arith)
                    requires cursor as int == i as int * n as int, n >= 1;
            };
            cursor = cursor + n;
            i += 1;
        }
        image
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
        assert!(lo <= hi);
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
    fn gen_binary(&mut self) -> i32 {
        (self.next_u64() % 2) as i32
    }
}

struct Solution;
include!("../code.rs");

fn make_flat(rng: &mut Rng, size: usize) -> Vec<i32> {
    let mut flat = Vec::with_capacity(size);
    for _ in 0..size {
        flat.push(rng.gen_binary());
    }
    flat
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    use std::io::Write;

    let mut rng = Rng::new(seed);
    let mut generated: usize = 0;

    // Example 1 from description: [[1,1,0],[1,0,1],[0,0,0]]
    {
        let image = vec![vec![1,1,0], vec![1,0,1], vec![0,0,0]];
        let result = Solution::flip_and_invert_image(image.clone());
        writeln!(out, "{}", json!({"input": {"image": image}, "output": result})).unwrap();
        generated += 1;
    }

    // Example 2 from description: [[1,1,0,0],[1,0,0,1],[0,1,1,1],[1,0,1,0]]
    {
        let image = vec![vec![1,1,0,0], vec![1,0,0,1], vec![0,1,1,1], vec![1,0,1,0]];
        let result = Solution::flip_and_invert_image(image.clone());
        writeln!(out, "{}", json!({"input": {"image": image}, "output": result})).unwrap();
        generated += 1;
    }

    // Generate remaining test cases with diverse sizes and mutations
    let num_mutations: u8 = 5; // 0..4
    while generated < count {
        // Size classes
        let n: usize = match generated % 5 {
            0 => 1,                                  // minimum
            1 => rng.gen_range_usize(1, 3),          // tiny
            2 => rng.gen_range_usize(4, 8),          // small
            3 => rng.gen_range_usize(9, 15),         // medium
            _ => rng.gen_range_usize(16, 20),        // max range
        };

        let flat = make_flat(&mut rng, n * n);
        let mutation_kind = (generated as u8) % num_mutations;

        let image = generate_test_case(n, flat, mutation_kind);
        let result = Solution::flip_and_invert_image(image.clone());
        writeln!(out, "{}", json!({"input": {"image": image}, "output": result})).unwrap();
        generated += 1;
    }
}
