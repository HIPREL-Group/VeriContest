use vstd::prelude::*;

verus! {

/// Generates a valid (colors, k) pair for the Alternating Groups II problem.
///
/// Construction parameters:
///   - `bits`: a Vec of i32 values used as raw material for colors (will be clamped to 0/1)
///   - `k_param`: raw k value (will be clamped to valid range)
///   - `mutation_kind`: selects different construction strategies
///
/// Ensures match the spec.rs requires exactly.
pub fn generate_test_case(
    bits: Vec<i32>,
    k_param: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32))
    requires
        3 <= bits.len() <= 100000,
        3 <= k_param,
    ensures
        3 <= result.0.len() <= 100000,
        3 <= result.1 <= result.0.len(),
        forall|i: int| 0 <= i < result.0.len() ==> (#[trigger] result.0[i] == 0 || result.0[i] == 1),
{
    // Build colors from bits: clamp each element to 0 or 1
    let n = bits.len();
    let mut colors: Vec<i32> = Vec::with_capacity(n);
    let mut idx: usize = 0;
    while idx < n
        invariant
            0 <= idx <= n,
            n == bits.len(),
            colors.len() == idx,
            3 <= n <= 100000,
            forall|j: int| 0 <= j < idx as int ==> (#[trigger] colors[j] == 0 || colors[j] == 1),
        decreases n - idx,
    {
        if bits[idx] % 2 == 0 {
            colors.push(0);
        } else {
            colors.push(1);
        }
        idx += 1;
    }

    // Apply mutation to colors
    if mutation_kind == 1 {
        // All same color (0)
        let mut i: usize = 0;
        while i < colors.len()
            invariant
                0 <= i <= colors.len(),
                colors.len() == n,
                3 <= n <= 100000,
                forall|j: int| 0 <= j < i as int ==> (#[trigger] colors[j] == 0),
                forall|j: int| i as int <= j < colors.len() ==> (#[trigger] colors[j] == 0 || colors[j] == 1),
            decreases colors.len() - i,
        {
            colors.set(i, 0);
            i += 1;
        }
    } else if mutation_kind == 2 {
        // All same color (1)
        let mut i: usize = 0;
        while i < colors.len()
            invariant
                0 <= i <= colors.len(),
                colors.len() == n,
                3 <= n <= 100000,
                forall|j: int| 0 <= j < i as int ==> (#[trigger] colors[j] == 1),
                forall|j: int| i as int <= j < colors.len() ==> (#[trigger] colors[j] == 0 || colors[j] == 1),
            decreases colors.len() - i,
        {
            colors.set(i, 1);
            i += 1;
        }
    } else if mutation_kind == 3 {
        // Perfect alternating starting with 0
        let mut i: usize = 0;
        while i < colors.len()
            invariant
                0 <= i <= colors.len(),
                colors.len() == n,
                3 <= n <= 100000,
                forall|j: int| 0 <= j < i as int ==> (#[trigger] colors[j] == (j % 2) as i32),
                forall|j: int| i as int <= j < colors.len() ==> (#[trigger] colors[j] == 0 || colors[j] == 1),
            decreases colors.len() - i,
        {
            colors.set(i, (i % 2) as i32);
            i += 1;
        }
    } else if mutation_kind == 4 {
        // Perfect alternating starting with 1
        let mut i: usize = 0;
        while i < colors.len()
            invariant
                0 <= i <= colors.len(),
                colors.len() == n,
                3 <= n <= 100000,
                forall|j: int| 0 <= j < i as int ==> (#[trigger] colors[j] == (1 - (j % 2) as i32)),
                forall|j: int| i as int <= j < colors.len() ==> (#[trigger] colors[j] == 0 || colors[j] == 1),
            decreases colors.len() - i,
        {
            colors.set(i, 1 - (i % 2) as i32);
            i += 1;
        }
    } else if mutation_kind == 5 && colors.len() > 0 {
        // Flip first element
        if colors[0] == 0 {
            colors.set(0, 1);
        } else {
            colors.set(0, 0);
        }
    } else if mutation_kind == 6 && colors.len() > 0 {
        // Flip last element
        let last = colors.len() - 1;
        if colors[last] == 0 {
            colors.set(last, 1);
        } else {
            colors.set(last, 0);
        }
    }
    // mutation_kind == 0 or fallback: identity (use clamped bits as-is)

    // Clamp k to valid range: 3 <= k <= colors.len()
    let cn = colors.len() as i32;
    let k: i32;
    if k_param > cn {
        k = cn;
    } else {
        k = k_param;
    }

    (colors, k)
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

fn random_colors(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(0, 1) as i32);
    }
    v
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(3208);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut num = 0usize;

    let mut emit = |colors: Vec<i32>, k: i32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, num: &mut usize| {
        if *num >= count {
            return;
        }
        let key = format!("{:?}_{}", colors, k);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::number_of_alternating_groups(colors.clone(), k);
        writeln!(out, "{}", json!({"input": {"colors": colors, "k": k}, "output": output})).unwrap();
        *num += 1;
    };

    // Example test cases from description.md
    {
        let (colors, k) = generate_test_case(vec![0, 1, 0, 1, 0], 3, 0);
        emit(colors, k, &mut seen, &mut out, &mut num);
    }
    {
        let (colors, k) = generate_test_case(vec![0, 1, 0, 0, 1, 0, 1], 6, 0);
        emit(colors, k, &mut seen, &mut out, &mut num);
    }
    {
        let (colors, k) = generate_test_case(vec![1, 1, 0, 1], 4, 0);
        emit(colors, k, &mut seen, &mut out, &mut num);
    }

    // Structured seeds × all mutations
    let structured_seeds: Vec<(Vec<i32>, i32)> = vec![
        (vec![0, 1, 0], 3),
        (vec![0, 0, 0], 3),
        (vec![1, 1, 1], 3),
        (vec![0, 1, 0, 1, 0, 1], 3),
        (vec![0, 1, 0, 1, 0, 1], 4),
        (vec![0, 1, 0, 1, 0, 1], 6),
        (vec![1, 0, 1, 0, 1, 0, 1, 0], 5),
        (vec![0, 0, 1, 1, 0, 0, 1, 1], 3),
        (vec![0, 1, 1, 0, 1, 0], 4),
    ];

    for (seed_colors, seed_k) in &structured_seeds {
        for mk in 0u8..7u8 {
            let (colors, k) = generate_test_case(seed_colors.clone(), *seed_k, mk);
            emit(colors, k, &mut seen, &mut out, &mut num);
        }
    }

    // Random test cases across size classes
    while num < count {
        let n: usize = match num % 5 {
            0 => rng.gen_range_usize(3, 5),       // tiny
            1 => rng.gen_range_usize(3, 10),      // small
            2 => rng.gen_range_usize(11, 100),     // medium
            3 => rng.gen_range_usize(101, 1000),   // large
            _ => rng.gen_range_usize(1001, 10000), // very large
        };
        let bits = random_colors(&mut rng, n);
        let k_raw = rng.gen_range_usize(3, n) as i32;
        let mk = rng.gen_range_usize(0, 6) as u8;
        let (colors, k) = generate_test_case(bits, k_raw, mk);
        emit(colors, k, &mut seen, &mut out, &mut num);
    }
}
