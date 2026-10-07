use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: usize, fill_val: i32, diag_val: i32, mutation_kind: u8) -> (result: Vec<Vec<i32>>)
    requires
        1 <= n <= 100,
        1 <= fill_val <= 100,
        1 <= diag_val <= 100,
    ensures
        1 <= result.len() <= 100,
        forall |i: int| 0 <= i < result.len() ==> (#[trigger] result[i]).len() == result.len(),
        forall |i: int, j: int| 0 <= i < result.len() && 0 <= j < result.len() ==> 1 <= #[trigger] result[i][j] <= 100,
{
    let fv: i32 = if mutation_kind == 0 {
        fill_val                                                    // identity
    } else if mutation_kind == 1 {
        1i32                                                        // min boundary
    } else if mutation_kind == 2 {
        100i32                                                      // max boundary
    } else if mutation_kind == 3 && fill_val < 100 {
        (fill_val + 1) as i32                                       // nudge up
    } else if mutation_kind == 4 && fill_val > 1 {
        (fill_val - 1) as i32                                       // nudge down
    } else if mutation_kind == 5 {
        ((fill_val + 1) / 2) as i32                                 // halve (rounds up, stays >= 1)
    } else if mutation_kind == 6 && fill_val <= 50 {
        (fill_val * 2) as i32                                       // double
    } else {
        fill_val                                                    // fallback
    };

    let dv: i32 = if mutation_kind == 7 {
        1i32                                                        // diag min
    } else if mutation_kind == 8 {
        100i32                                                      // diag max
    } else if mutation_kind == 9 {
        fv                                                          // diag = fill (uniform matrix)
    } else {
        diag_val
    };

    let mut mat: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            mat.len() == i,
            1 <= n <= 100,
            1 <= fv <= 100,
            1 <= dv <= 100,
            forall |r: int| 0 <= r < i ==> (#[trigger] mat[r]).len() == n,
            forall |r: int, c: int| 0 <= r < i && 0 <= c < n ==> 1 <= #[trigger] mat[r][c] <= 100,
        decreases n - i,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j <= n,
                row.len() == j,
                1 <= fv <= 100,
                1 <= dv <= 100,
                forall |c: int| 0 <= c < j ==> 1 <= #[trigger] row[c] <= 100,
            decreases n - j,
        {
            if j == i {
                row.push(dv);
            } else {
                row.push(fv);
            }
            j += 1;
        }
        mat.push(row);
        i += 1;
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

    fn gen_u8(&mut self) -> u8 {
        (self.next_u64() % 256) as u8
    }
}

struct Solution;
include!("../code.rs");

fn random_matrix(rng: &mut Rng, n: usize) -> Vec<Vec<i32>> {
    let mut mat = Vec::with_capacity(n);
    for _ in 0..n {
        let mut row = Vec::with_capacity(n);
        for _ in 0..n {
            row.push(rng.gen_range_i64(1, 100) as i32);
        }
        mat.push(row);
    }
    mat
}

fn main() {
    use std::io::Write;
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut count = 0usize;

    // Helper closure to emit a test case
    let mut emit = |mat: Vec<Vec<i32>>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= goal { return; }
        let result = Solution::diagonal_sum(mat.clone());
        writeln!(out, "{}", json!({"input": {"mat": mat}, "output": result})).unwrap();
        *count += 1;
    };

    // Example test cases from description.md
    emit(vec![vec![1,2,3], vec![4,5,6], vec![7,8,9]], &mut out, &mut count);
    emit(vec![vec![1,1,1,1], vec![1,1,1,1], vec![1,1,1,1], vec![1,1,1,1]], &mut out, &mut count);
    emit(vec![vec![5]], &mut out, &mut count);

    // Seed pools for construction parameters
    let sizes: Vec<usize> = vec![1, 2, 3, 4, 5, 10, 20, 50, 99, 100];
    let fill_vals: Vec<i32> = vec![1, 2, 50, 99, 100];
    let diag_vals: Vec<i32> = vec![1, 2, 50, 99, 100];
    let mutation_kinds: Vec<u8> = (0..=9).collect();

    // Systematic: sizes × fill_vals × diag_vals × mutation_kinds (sample)
    for &n in &sizes {
        for &fv in &fill_vals {
            for &dv in &diag_vals {
                for &mk in &mutation_kinds {
                    if count >= goal { break; }
                    let mat = generate_test_case(n, fv, dv, mk);
                    emit(mat, &mut out, &mut count);
                }
            }
        }
    }

    // Random test cases with diverse sizes
    while count < goal {
        let n = match rng.gen_u8() % 5 {
            0 => rng.gen_range_usize(1, 3),       // tiny
            1 => rng.gen_range_usize(1, 10),       // small
            2 => rng.gen_range_usize(11, 30),      // medium
            3 => rng.gen_range_usize(31, 70),      // large
            _ => rng.gen_range_usize(71, 100),     // max
        };
        let fv = rng.gen_range_i64(1, 100) as i32;
        let dv = rng.gen_range_i64(1, 100) as i32;
        let mk = rng.gen_u8() % 10;
        let mat = generate_test_case(n, fv, dv, mk);
        emit(mat, &mut out, &mut count);
    }
}
