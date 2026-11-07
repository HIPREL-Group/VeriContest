use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: &mut Vec<i32>, mutation_kind: u8)
    requires
        1 <= old(nums).len() <= 300,
        forall|i: int| 0 <= i < old(nums).len() ==> 0 <= #[trigger] old(nums)[i] <= 2,
    ensures
        1 <= old(nums).len() <= 300,
        forall|i: int| 0 <= i < old(nums).len() ==> 0 <= #[trigger] old(nums)[i] <= 2,
{
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

fn mutate(mut nums: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(&mut nums, mutation_kind);
    nums
}

extern crate serde_json;
use serde_json::json;

fn random_colors(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(0, 2) as i32);
    }
    v
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(75);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target {
            return;
        }
        let key = format!("{:?}", nums);
        if !seen.insert(key) {
            return;
        }
        let mut input = nums.clone();
        Solution::sort_colors(&mut input);
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": input})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![2, 0, 2, 1, 1, 0],
        vec![2, 0, 1],
    ];
    for ex in &examples {
        emit(ex.clone(), &mut seen, &mut out, &mut count);
    }

    // Hand-crafted seed inputs for diversity
    let seeds: Vec<Vec<i32>> = vec![
        vec![0],
        vec![1],
        vec![2],
        vec![0, 0],
        vec![1, 1],
        vec![2, 2],
        vec![0, 1, 2],
        vec![2, 1, 0],
        vec![0, 0, 0],
        vec![1, 1, 1],
        vec![2, 2, 2],
        vec![0, 2, 1, 0, 2, 1],
        vec![2, 2, 1, 1, 0, 0],
        vec![0, 0, 1, 1, 2, 2],  // already sorted
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    // Apply every mutation to every seed
    for s in &seeds {
        for &mk in &mutation_kinds {
            let result = mutate(s.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random inputs with diverse size classes and random mutations
    for i in 0..200 {
        if count >= target { break; }
        let len: usize = match i % 5 {
            0 => rng.gen_range_usize(1, 5),       // tiny
            1 => rng.gen_range_usize(1, 10),      // small
            2 => rng.gen_range_usize(11, 50),     // medium
            3 => rng.gen_range_usize(51, 150),    // large
            _ => rng.gen_range_usize(151, 300),   // max
        };
        let seed_arr = random_colors(&mut rng, len);
        let mk = rng.gen_range_usize(0, 9) as u8;
        let result = mutate(seed_arr, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }

    // Fill remaining with random identity inputs
    while count < target {
        let len = rng.gen_range_usize(1, 300);
        let arr = random_colors(&mut rng, len);
        emit(mutate(arr, 0), &mut seen, &mut out, &mut count);
    }
}
