use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    values: &Vec<i32>,
    mutation_kind: u8,
) -> (result: Vec<Vec<i32>>)
    requires
        1 <= n <= 300,
        values.len() == n * n,
        forall|k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 4_000_000i32,
    ensures
        1 <= result.len() <= 300,
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i].len() == result.len(),
        forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result[i].len() ==> 1 <= #[trigger] result[i][j] <= 4_000_000i32,
{
    let mut matrix: Vec<Vec<i32>> = Vec::new();
    let mut r: usize = 0;
    while r < n
        invariant
            0 <= r <= n,
            1 <= n <= 300,
            matrix.len() == r as int,
            values.len() == n * n,
            forall|k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 4_000_000i32,
            forall|i: int| 0 <= i < r ==> (#[trigger] matrix[i]).len() == n,
            forall|i: int, j: int|
                0 <= i < r && 0 <= j < n ==>
                1 <= #[trigger] matrix[i][j] <= 4_000_000i32,
        decreases n - r,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut c: usize = 0;
        while c < n
            invariant
                0 <= c <= n,
                0 <= r < n,
                1 <= n <= 300,
                row.len() == c as int,
                values.len() == n * n,
                forall|k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 4_000_000i32,
                forall|j: int| 0 <= j < c ==> 1 <= #[trigger] row[j] <= 4_000_000i32,
            decreases n - c,
        {
            assert(r * n + c < n * n) by {
                assert(r < n);
                assert(c < n);
                assert(r * n <= (n - 1) * n) by (nonlinear_arith)
                    requires r < n, 1 <= n <= 300;
                assert((n - 1) * n + c < n * n) by (nonlinear_arith)
                    requires c < n, 1 <= n <= 300;
            };
            let idx: usize = r * n + c;
            let val: i32 = if mutation_kind == 1 && (c == r || c == n - 1 - r) {
                // Place small prime 2 on both diagonals
                2i32
            } else if mutation_kind == 2 {
                // All elements are 1 (not prime) — result should be 0
                1i32
            } else if mutation_kind == 3 && (c == r || c == n - 1 - r) {
                // Place large value 3_999_989 (a prime near max) on diagonals
                3_999_989i32
            } else if mutation_kind == 4 && c == r {
                // Place 4_000_000 on main diagonal (not prime)
                4_000_000i32
            } else {
                values[idx]
            };
            row.push(val);
            c += 1;
        }
        matrix.push(row);

        assert(matrix[r as int].len() == n);

        proof {
            assert forall|i: int| 0 <= i < r + 1 implies (#[trigger] matrix[i]).len() == n by {
                if i < r as int {
                } else {
                    assert(i == r as int);
                    assert(matrix[i].len() == n);
                }
            };
            assert forall|i: int, j: int|
                0 <= i < r + 1 && 0 <= j < n implies
                1 <= #[trigger] matrix[i][j] <= 4_000_000i32 by {
                if i < r as int {
                } else {
                    assert(i == r as int);
                }
            };
        }

        r += 1;
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

fn random_flat_values(rng: &mut Rng, count: usize, lo: i32, hi: i32) -> Vec<i32> {
    let mut vals = Vec::with_capacity(count);
    for _ in 0..count {
        vals.push(rng.gen_range_i64(lo as i64, hi as i64) as i32);
    }
    vals
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2614);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<Vec<i32>>,
                    seen: &mut HashSet<String>,
                    out: &mut std::io::BufWriter<std::fs::File>,
                    count: &mut usize| {
        if *count >= target {
            return;
        }
        let key = format!("{:?}", nums);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::diagonal_prime(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // --- Example test cases from description.md ---
    emit(
        vec![vec![1, 2, 3], vec![5, 6, 7], vec![9, 10, 11]],
        &mut seen, &mut out, &mut count,
    );
    emit(
        vec![vec![1, 2, 3], vec![5, 17, 7], vec![9, 11, 10]],
        &mut seen, &mut out, &mut count,
    );

    // --- Edge case: 1x1 matrix ---
    for v in [1, 2, 3, 4, 7, 4_000_000] {
        let vals = vec![v];
        let nums = generate_test_case(1, &vals, 0);
        emit(nums, &mut seen, &mut out, &mut count);
    }

    // --- Small matrices with all mutation kinds ---
    let small_primes: Vec<i32> = vec![2, 3, 5, 7, 11, 13, 17, 19, 23];
    for mk in 0u8..=4 {
        // 3x3 with small primes on diag
        let vals: Vec<i32> = (0..9).map(|i| small_primes[i % small_primes.len()]).collect();
        let nums = generate_test_case(3, &vals, mk);
        emit(nums, &mut seen, &mut out, &mut count);

        // 2x2
        let vals: Vec<i32> = vec![2, 3, 5, 7];
        let nums = generate_test_case(2, &vals, mk);
        emit(nums, &mut seen, &mut out, &mut count);
    }

    // --- Boundary values ---
    // All 1s (no primes)
    for n in [1, 2, 5, 10] {
        let vals = vec![1i32; n * n];
        let nums = generate_test_case(n, &vals, 0);
        emit(nums, &mut seen, &mut out, &mut count);
    }

    // All max value
    for n in [1, 2, 3] {
        let vals = vec![4_000_000i32; n * n];
        let nums = generate_test_case(n, &vals, 0);
        emit(nums, &mut seen, &mut out, &mut count);
    }

    // --- Diverse random test cases with size classes ---
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4];
    while count < target {
        let n: usize = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 3),        // tiny
            1 => rng.gen_range_usize(1, 10),        // small
            2 => rng.gen_range_usize(11, 50),       // medium
            3 => rng.gen_range_usize(51, 150),      // large
            _ => rng.gen_range_usize(151, 300),     // max
        };
        let mk = mutation_kinds[rng.gen_range_usize(0, mutation_kinds.len() - 1)];

        // Mix boundary and random values
        let vals = if rng.gen_range_usize(0, 4) == 0 {
            // ~20%: use boundary-heavy values
            random_flat_values(&mut rng, n * n, 1, 10)
        } else {
            random_flat_values(&mut rng, n * n, 1, 4_000_000)
        };

        let nums = generate_test_case(n, &vals, mk);
        emit(nums, &mut seen, &mut out, &mut count);
    }
}
