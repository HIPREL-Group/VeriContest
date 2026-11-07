use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= nums.len() <= 100,
        nums.len() % 2 == 0,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
    ensures
        1 <= result.len() <= 100,
        result.len() % 2 == 0,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 100,
{
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 {
        // set first element to boundary low (1)
        let mut n = nums;
        n.set(0, 1);
        n
    } else if mutation_kind == 2 {
        // set first element to boundary high (100)
        let mut n = nums;
        n.set(0, 100);
        n
    } else if mutation_kind == 3 {
        // set all elements to 50 (forces many duplicates)
        let mut n = nums;
        let mut i: usize = 0;
        while i < n.len()
            invariant
                0 <= i <= n.len(),
                n.len() == nums.len(),
                1 <= n.len() <= 100,
                n.len() % 2 == 0,
                forall|j: int| 0 <= j < i ==> n[j] == 50,
                forall|j: int| i <= j < n.len() ==> n[j] == nums[j],
            decreases n.len() - i,
        {
            n.set(i, 50);
            i += 1;
        }
        n
    } else if mutation_kind == 4 && nums.len() >= 2 {
        // swap first two elements
        let mut n = nums;
        let a = n[0];
        let b = n[1];
        n.set(0, b);
        n.set(1, a);
        n
    } else if mutation_kind == 5 {
        // nudge first element up (if < 100)
        let mut n = nums;
        if n[0] < 100 {
            n.set(0, n[0] + 1);
        }
        n
    } else if mutation_kind == 6 {
        // nudge first element down (if > 1)
        let mut n = nums;
        if n[0] > 1 {
            n.set(0, n[0] - 1);
        }
        n
    } else if mutation_kind == 7 {
        // set last element to 1
        let mut n = nums;
        let last = n.len() - 1;
        n.set(last, 1);
        n
    } else {
        // fallback: identity
        nums
    }
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
}

struct Solution;
include!("../code.rs");

fn mutate(nums: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(nums, mutation_kind)
}

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(1, 100) as i32);
    }
    nums
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        let key = format!("{:?}", nums);
        if !seen.insert(key) { return; }
        let output = Solution::is_possible_to_split(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Seed inputs: examples from description.md + interesting edge cases
    let seeds: Vec<Vec<i32>> = vec![
        vec![1, 1, 2, 2, 3, 4],             // example 1 (true)
        vec![1, 1, 1, 1],                     // example 2 (false)
        vec![1, 2],                            // minimum even length
        vec![1, 1],                            // minimum, one duplicate
        vec![50, 50, 50, 50, 50, 50],         // all same, 6 elements (false)
        vec![1, 100],                          // boundary values
        vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10], // all unique (true)
        vec![1, 1, 2, 2, 3, 3],               // each appears exactly twice (true)
        vec![1, 1, 1, 2, 2, 2],               // two triples (false)
        vec![100, 100, 100, 1, 1, 1],         // boundary triples (false)
        vec![1, 2, 3, 4],                      // small all unique
        vec![99, 100, 99, 100],               // two pairs at high boundary
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7];

    // Apply every mutation to every seed
    for seed in &seeds {
        for &mk in &mutation_kinds {
            let result = mutate(seed.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random inputs with diverse size classes
    while count < target {
        let half = match rng.gen_range_usize(0, 4) {
            0 => 1,                                // len = 2
            1 => rng.gen_range_usize(1, 5),        // len = 2..10
            2 => rng.gen_range_usize(6, 25),       // len = 12..50
            3 => rng.gen_range_usize(26, 50),      // len = 52..100
            _ => 50,                               // len = 100
        };
        let len = half * 2;
        let nums = random_nums(&mut rng, len);
        let mk = rng.gen_range_usize(0, 8) as u8;
        let result = mutate(nums, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }
}
