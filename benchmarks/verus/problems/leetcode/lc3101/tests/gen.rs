use vstd::prelude::*;

verus! {

struct Gen;

impl Gen {
    /// Build a binary array of length actual_n using the given pattern.
    /// pattern == 0 => all 0s
    /// pattern == 1 => all 1s
    /// pattern == 2 => alternating starting with 0
    /// pattern == 3 => alternating starting with 1
    /// other        => all 0s (fallback)
    ///
    /// mutation_kind mutates the length parameter for diversity.
    pub fn generate_test_case(n: usize, pattern: u8, mutation_kind: u8) -> (nums: Vec<i32>)
        requires
            1 <= n <= 100000,
        ensures
            1 <= nums.len() <= 100000,
            forall |i: int| 0 <= i < nums.len() ==> (#[trigger] nums[i] == 0 || #[trigger] nums[i] == 1),
    {
        // Mutate the length parameter
        let actual_n: usize = if mutation_kind == 1 && n >= 2 {
            n / 2
        } else if mutation_kind == 2 && n <= 50000 {
            n * 2
        } else if mutation_kind == 3 {
            1
        } else if mutation_kind == 4 && n <= 99999 {
            n + 1
        } else if mutation_kind == 5 && n >= 2 {
            n - 1
        } else if mutation_kind == 6 {
            100000
        } else {
            n
        };

        let mut nums: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < actual_n
            invariant
                0 <= i <= actual_n,
                1 <= actual_n <= 100000,
                nums.len() == i as int,
                forall |j: int| 0 <= j < i as int ==> (#[trigger] nums[j] == 0 || #[trigger] nums[j] == 1),
            decreases actual_n - i,
        {
            let val: i32 = if pattern == 0 {
                0
            } else if pattern == 1 {
                1
            } else if pattern == 2 {
                // alternating starting with 0: 0,1,0,1,...
                if i % 2 == 0 { 0 } else { 1 }
            } else if pattern == 3 {
                // alternating starting with 1: 1,0,1,0,...
                if i % 2 == 0 { 1 } else { 0 }
            } else {
                0
            };
            nums.push(val);
            i = i + 1;
        }

        nums
    }
}

} // verus!

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
}

struct Solution;
include!("../code.rs");

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(3101);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);

    let mut count = 0usize;
    let mut seen = HashSet::<String>::new();

    let mut emit = |nums: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        let key = format!("{:?}", nums);
        if !seen.insert(key) { return; }
        let output = Solution::count_alternating_subarrays(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![0, 1, 1, 1],
        vec![1, 0, 1, 0],
    ];
    for ex in examples {
        emit(ex, &mut seen, &mut out, &mut count);
    }

    // Boundary: single-element arrays
    emit(vec![0], &mut seen, &mut out, &mut count);
    emit(vec![1], &mut seen, &mut out, &mut count);

    // Two-element arrays
    emit(vec![0, 0], &mut seen, &mut out, &mut count);
    emit(vec![0, 1], &mut seen, &mut out, &mut count);
    emit(vec![1, 0], &mut seen, &mut out, &mut count);
    emit(vec![1, 1], &mut seen, &mut out, &mut count);

    // Generator-based: diverse (n, pattern, mutation_kind) combinations
    let patterns: Vec<u8> = vec![0, 1, 2, 3, 4];
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7];

    // Structured sweep: small sizes x all patterns x all mutations
    for &pat in &patterns {
        for &mk in &mutation_kinds {
            if count >= target { break; }
            let n = rng.gen_range_usize(1, 20);
            let result = Gen::generate_test_case(n, pat, mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Fill remaining with random combinations across size classes
    while count < target {
        let n = match count % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(5, 50),
            2 => rng.gen_range_usize(50, 500),
            3 => rng.gen_range_usize(500, 5000),
            _ => rng.gen_range_usize(5000, 50000),
        };
        let pat = rng.gen_range_usize(0, 4) as u8;
        let mk = rng.gen_range_usize(0, 7) as u8;
        let result = Gen::generate_test_case(n, pat, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }

    eprintln!("Generated {} test cases", count);
}
