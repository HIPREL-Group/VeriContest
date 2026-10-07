use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        2 <= nums.len() <= 100,
        nums.len() % 2 == 0,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
    ensures
        2 <= result.len() <= 100,
        result.len() % 2 == 0,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 100,
{
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 {
        // set first element to min boundary (1)
        let mut d = nums;
        d.set(0, 1);
        d
    } else if mutation_kind == 2 {
        // set first element to max boundary (100)
        let mut d = nums;
        d.set(0, 100);
        d
    } else if mutation_kind == 3 {
        // set all elements to 50
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                2 <= d.len() <= 100,
                d.len() % 2 == 0,
                forall|j: int| 0 <= j < i ==> d[j] == 50,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 50);
            i += 1;
        }
        d
    } else if mutation_kind == 4 && nums.len() >= 2 {
        // swap first two elements
        let mut d = nums;
        let tmp = d[0];
        d.set(0, d[1]);
        d.set(1, tmp);
        d
    } else if mutation_kind == 5 && nums.len() <= 98 {
        // grow by 2 (push two elements to keep even length)
        let mut d = nums;
        d.push(1);
        d.push(1);
        d
    } else if mutation_kind == 6 && nums.len() > 2 {
        // shrink by 2 (pop two elements to keep even length)
        let mut d = nums;
        d.pop();
        d.pop();
        d
    } else if mutation_kind == 7 {
        // nudge first element up (if < 100)
        let mut d = nums;
        if d[0] < 100 {
            d.set(0, d[0] + 1);
        }
        d
    } else if mutation_kind == 8 {
        // nudge first element down (if > 1)
        let mut d = nums;
        if d[0] > 1 {
            d.set(0, d[0] - 1);
        }
        d
    } else if mutation_kind == 9 {
        // set last element to 1
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 1);
        d
    } else if mutation_kind == 10 {
        // set last element to 100
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 100);
        d
    } else {
        // fallback: identity
        nums
    }
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

fn mutate(nums: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(nums, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

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
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2974);
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
        let output = Solution::number_game(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![5, 4, 2, 3],
        vec![2, 5],
    ];

    // Seed pool: various interesting arrays
    let seeds: Vec<Vec<i32>> = vec![
        vec![1, 1],                             // min length, min values
        vec![100, 100],                         // min length, max values
        vec![1, 100],                           // min/max mix
        vec![100, 1],                           // reversed
        vec![50, 50],                           // same value
        vec![1, 2, 3, 4],                       // sorted ascending
        vec![4, 3, 2, 1],                       // sorted descending
        vec![1, 1, 1, 1, 1, 1],                // all same, min
        vec![100, 100, 100, 100, 100, 100],    // all same, max
        vec![1, 100, 1, 100, 1, 100],          // alternating min/max
        vec![50, 51, 50, 51],                   // near-equal values
        vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10],  // consecutive 1..10
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

    // Emit examples first (identity mutation)
    for ex in &examples {
        emit(ex.clone(), &mut seen, &mut out, &mut count);
    }

    // Apply every mutation to every seed
    for seed_arr in &seeds {
        for &mk in &mutation_kinds {
            let result = mutate(seed_arr.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds with random mutations across size classes
    while count < target {
        let len = match count % 5 {
            0 => 2,                                            // tiny (min)
            1 => rng.gen_range_usize(1, 5) * 2,               // small
            2 => rng.gen_range_usize(5, 25) * 2,              // medium
            3 => rng.gen_range_usize(25, 45) * 2,             // large
            _ => rng.gen_range_usize(45, 50) * 2,             // max
        };
        let seed_arr = random_nums(&mut rng, len);
        let mk = rng.gen_range_usize(0, 10) as u8;
        let result = mutate(seed_arr, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }
}
