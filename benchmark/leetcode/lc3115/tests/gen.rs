use vstd::prelude::*;

verus! {

/// Mirrors `Solution::is_prime` from spec.rs so the ensures can reference it.
pub open spec fn is_prime(n: int) -> bool {
    n == 2 || n == 3 || n == 5 || n == 7 || n == 11 || n == 13 || n == 17 || n == 19
        || n == 23 || n == 29 || n == 31 || n == 37 || n == 41 || n == 43 || n == 47
        || n == 53 || n == 59 || n == 61 || n == 67 || n == 71 || n == 73 || n == 79
        || n == 83 || n == 89 || n == 97
}

/// Constructs a valid input for `maximum_prime_difference`.
///
/// Construction parameters:
///   - `nums`         : base array with elements in [1,100]
///   - `prime_idx`    : position where we guarantee a prime is placed
///   - `prime_val`    : the prime value to place (must satisfy `is_prime`)
///   - `mutation_kind`: selects a structural mutation applied after placing the prime
///
/// The generator places `prime_val` at `prime_idx`, then optionally mutates
/// other positions to create diverse test scenarios (primes at ends, single
/// prime, etc.).  Every branch preserves all three spec requires.
pub fn generate_test_case(
    nums: Vec<i32>,
    prime_idx: usize,
    prime_val: i32,
    mutation_kind: u8,
) -> (result: Vec<i32>)
    requires
        1 <= nums.len() <= 300000,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
        prime_idx < nums.len(),
        is_prime(prime_val as int),
        1 <= prime_val <= 100,
    ensures
        1 <= result.len() <= 300000,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 100,
        exists|i: int| 0 <= i < result.len() && is_prime(result[i] as int),
{
    let mut r = nums;
    r.set(prime_idx, prime_val);

    if mutation_kind == 1 && prime_idx > 0 {
        // Also place prime at position 0
        r.set(0, prime_val);
    } else if mutation_kind == 2 && prime_idx + 1 < r.len() {
        // Also place prime at last position
        let last = r.len() - 1;
        r.set(last, prime_val);
    } else if mutation_kind == 3 && r.len() >= 2 {
        // Primes at both ends
        let last = r.len() - 1;
        r.set(0, prime_val);
        r.set(last, prime_val);
    } else if mutation_kind == 4 && prime_idx > 0 {
        // Set position 0 to a non-prime (4) — tests leftward scan
        r.set(0, 4);
    } else if mutation_kind == 5 && prime_idx + 1 < r.len() {
        // Set last position to a non-prime (4) — tests rightward scan
        let last = r.len() - 1;
        r.set(last, 4);
    } else if mutation_kind == 6 && r.len() >= 2 && prime_idx > 0 && prime_idx + 1 < r.len() {
        // Non-prime at both ends
        let last = r.len() - 1;
        r.set(0, 4);
        r.set(last, 4);
    }
    // mutation_kind == 0 or fallback: identity after placing prime

    assert(is_prime(r[prime_idx as int] as int));
    r
}

} // verus!

// ---------------------------------------------------------------------------
// Runtime helpers (not verified)
// ---------------------------------------------------------------------------

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let range = (hi as i64 - lo as i64 + 1) as u64;
        (lo as i64 + (self.next_u64() % range) as i64) as i32
    }
}

struct Solution;
include!("../code.rs");

fn mutate(nums: Vec<i32>, prime_idx: usize, prime_val: i32, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(nums, prime_idx, prime_val, mutation_kind)
}

const PRIMES: [i32; 25] = [
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47,
    53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
];

extern crate serde_json;
use serde_json::json;

fn random_array(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i32(1, 100));
    }
    v
}

fn main() {
    use std::io::Write;
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(3115);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut count: usize = 0;

    let mut emit = |nums: Vec<i32>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        let output = Solution::maximum_prime_difference(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // ---- Example inputs from description.md ----
    emit(vec![4, 2, 9, 5, 3], &mut out, &mut count);
    emit(vec![4, 8, 2, 8], &mut out, &mut count);

    // ---- Crafted edge cases ----
    // Single element (prime)
    emit(vec![2], &mut out, &mut count);
    emit(vec![97], &mut out, &mut count);
    // Single prime among non-primes
    emit(vec![4, 6, 8, 2, 10, 12], &mut out, &mut count);
    // Primes at both ends
    emit(vec![2, 4, 6, 8, 3], &mut out, &mut count);
    // All primes
    emit(vec![2, 3, 5, 7, 11, 13], &mut out, &mut count);
    // Prime only at first position
    emit(vec![2, 4, 6, 8, 10], &mut out, &mut count);
    // Prime only at last position
    emit(vec![4, 6, 8, 10, 97], &mut out, &mut count);
    // Two primes adjacent
    emit(vec![4, 4, 2, 3, 4, 4], &mut out, &mut count);
    // Two primes far apart
    emit(vec![2, 4, 4, 4, 4, 4, 4, 4, 4, 3], &mut out, &mut count);

    // ---- Systematic: every mutation kind × size classes ----
    let mutation_kinds: [u8; 7] = [0, 1, 2, 3, 4, 5, 6];
    let size_classes: [usize; 5] = [1, 5, 50, 500, 5000];

    for &sz in &size_classes {
        for &mk in &mutation_kinds {
            if count >= target { break; }
            let nums = random_array(&mut rng, sz);
            let prime_idx = rng.gen_range_usize(0, sz - 1);
            let prime_val = PRIMES[rng.gen_range_usize(0, PRIMES.len() - 1)];
            let result = mutate(nums, prime_idx, prime_val, mk);
            emit(result, &mut out, &mut count);
        }
    }

    // ---- Random tests to fill remaining ----
    while count < target {
        let sz = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 5),        // tiny
            1 => rng.gen_range_usize(1, 10),        // small
            2 => rng.gen_range_usize(11, 100),      // medium
            3 => rng.gen_range_usize(101, 1000),    // large
            _ => rng.gen_range_usize(1001, 10000),  // very large
        };
        let nums = random_array(&mut rng, sz);
        let prime_idx = rng.gen_range_usize(0, sz - 1);
        let prime_val = PRIMES[rng.gen_range_usize(0, PRIMES.len() - 1)];
        let mk = rng.gen_range_usize(0, 6) as u8;
        let result = mutate(nums, prime_idx, prime_val, mk);
        emit(result, &mut out, &mut count);
    }

    eprintln!("Generated {} test cases → {:?}", count, out_path);
}
