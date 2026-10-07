use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    m: usize,
    n: usize,
    k_val: i32,
    row_ones: &Vec<i32>,
    mutation_kind: u8,
) -> (result: (Vec<Vec<i32>>, i32))
    requires
        2 <= m <= 100,
        2 <= n <= 100,
        1 <= k_val <= m as i32,
        row_ones.len() == m,
        forall|i: int| 0 <= i < m as int ==> 0 <= #[trigger] row_ones[i] <= n as i32,
    ensures
        2 <= result.0.len() <= 100,
        forall|i: int| 0 <= i < result.0.len() ==> 2 <= (#[trigger] result.0[i]).len() <= 100,
        forall|i: int| 0 <= i < result.0.len() ==> (#[trigger] result.0[i]).len() == result.0[0].len(),
        1 <= result.1 <= result.0.len() as i32,
        forall|i: int, j: int| 0 <= i < result.0.len() && 0 <= j < result.0[i].len()
            ==> #[trigger] result.0[i][j] == 0 || result.0[i][j] == 1,
{
    let mut mat: Vec<Vec<i32>> = Vec::new();
    let mut ri: usize = 0;

    while ri < m
        invariant
            0 <= ri <= m,
            2 <= m <= 100,
            2 <= n <= 100,
            mat.len() == ri,
            row_ones.len() == m,
            forall|i: int| 0 <= i < m as int ==> 0 <= #[trigger] row_ones[i] <= n as i32,
            forall|i: int| 0 <= i < ri as int ==> (#[trigger] mat[i]).len() == n,
            forall|i: int, j: int| 0 <= i < ri as int && 0 <= j < n as int
                ==> (#[trigger] mat[i][j] == 0 || mat[i][j] == 1),
        decreases m - ri,
    {
        let ones: usize = if mutation_kind == 3 {
            0usize
        } else if mutation_kind == 4 {
            n
        } else {
            row_ones[ri] as usize
        };

        assert(ones <= n);

        let mut row: Vec<i32> = Vec::new();
        let mut ci: usize = 0;

        while ci < n
            invariant
                0 <= ci <= n,
                2 <= n <= 100,
                row.len() == ci,
                ones <= n,
                forall|j: int| 0 <= j < ci as int ==> (#[trigger] row[j] == 0 || row[j] == 1),
            decreases n - ci,
        {
            if ci < ones {
                row.push(1);
            } else {
                row.push(0);
            }
            ci += 1;
        }

        assert(row.len() == n);

        mat.push(row);
        ri += 1;

        proof {
            assert(mat[ri as int - 1].len() == n);
            assert forall|i: int| 0 <= i < ri as int implies (#[trigger] mat[i]).len() == n by {
                if i < ri as int - 1 {
                } else {
                    assert(mat[ri as int - 1].len() == n);
                }
            };
            assert forall|i: int, j: int|
                0 <= i < ri as int && 0 <= j < n as int
                implies (#[trigger] mat[i][j] == 0 || mat[i][j] == 1) by {
                if i < ri as int - 1 {
                } else {
                }
            };
        }
    }

    assert(mat.len() == m);
    assert(2 <= mat.len() <= 100);

    proof {
        assert(mat[0].len() == n);
        assert forall|i: int| 0 <= i < mat.len() implies (#[trigger] mat[i]).len() == mat[0].len() by {
            assert(mat[i].len() == n);
            assert(mat[0].len() == n);
        };

        assert forall|i: int, j: int|
            0 <= i < mat.len() && 0 <= j < mat[i].len()
            implies (#[trigger] mat[i][j] == 0 || mat[i][j] == 1) by {
            assert(mat[i].len() == n);
        };
    }

    let k_out: i32 = if mutation_kind == 1 {
        1i32
    } else if mutation_kind == 2 {
        m as i32
    } else {
        k_val
    };

    (mat, k_out)
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

fn main() {
    use std::io::Write;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1337);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut total = 0usize;

    let mut emit = |mat: Vec<Vec<i32>>, k: i32, out: &mut std::io::BufWriter<std::fs::File>, total: &mut usize| {
        if *total >= count { return; }
        let result = Solution::k_weakest_rows(mat.clone(), k);
        let mat_json: Vec<Vec<i32>> = mat;
        writeln!(out, "{}", json!({"input": {"mat": mat_json, "k": k}, "output": result})).unwrap();
        *total += 1;
    };

    // Example 1 from description.md
    {
        let mat = vec![
            vec![1,1,0,0,0],
            vec![1,1,1,1,0],
            vec![1,0,0,0,0],
            vec![1,1,0,0,0],
            vec![1,1,1,1,1],
        ];
        emit(mat, 3, &mut out, &mut total);
    }

    // Example 2 from description.md
    {
        let mat = vec![
            vec![1,0,0,0],
            vec![1,1,1,1],
            vec![1,0,0,0],
            vec![1,0,0,0],
        ];
        emit(mat, 2, &mut out, &mut total);
    }

    // Generate diverse test cases via generate_test_case
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4];

    while total < count {
        // Size classes for m
        let m: usize = match total % 5 {
            0 => rng.gen_range_usize(2, 3),     // tiny
            1 => rng.gen_range_usize(2, 5),     // small
            2 => rng.gen_range_usize(6, 20),    // medium
            3 => rng.gen_range_usize(21, 50),   // large
            _ => rng.gen_range_usize(51, 100),  // max
        };

        // Size classes for n
        let n: usize = match total % 7 {
            0 => 2,                              // minimum
            1 => rng.gen_range_usize(2, 5),      // small
            2 => rng.gen_range_usize(6, 20),     // medium
            3 => rng.gen_range_usize(21, 50),    // large
            4 => rng.gen_range_usize(51, 100),   // big
            5 => 100,                            // maximum
            _ => rng.gen_range_usize(2, 100),    // random
        };

        // k value with boundary emphasis
        let k: i32 = match total % 4 {
            0 => 1,                                        // minimum
            1 => m as i32,                                 // maximum
            2 => rng.gen_range_i64(1, m as i64) as i32,    // random
            _ => ((m as i32) / 2).max(1),                  // middle
        };

        // Build row_ones
        let mut row_ones: Vec<i32> = Vec::with_capacity(m);
        for _ in 0..m {
            // Mix boundary values in ~20% of cases
            let ones: i32 = if rng.gen_range_usize(0, 4) == 0 {
                // Boundary: 0 or n
                if rng.gen_range_usize(0, 1) == 0 { 0 } else { n as i32 }
            } else {
                rng.gen_range_i64(0, n as i64) as i32
            };
            row_ones.push(ones);
        }

        let mk = mutation_kinds[total % mutation_kinds.len()];
        let (mat, k_out) = generate_test_case(m, n, k, &row_ones, mk);
        emit(mat, k_out, &mut out, &mut total);
    }
}
