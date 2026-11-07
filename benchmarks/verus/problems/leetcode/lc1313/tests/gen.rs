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
        // set last element to 1 (min boundary)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 1);
        d
    } else if mutation_kind == 2 {
        // set last element to 100 (max boundary)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 100);
        d
    } else if mutation_kind == 3 {
        // set first element to 1 (freq = 1)
        let mut d = nums;
        d.set(0, 1);
        d
    } else if mutation_kind == 4 && nums.len() <= 98 {
        // grow by 2 elements (push a pair [1, 50])
        let mut d = nums;
        d.push(1);
        d.push(50);
        d
    } else if mutation_kind == 5 && nums.len() > 2 {
        // shrink by 2 elements (pop last pair)
        let mut d = nums;
        d.pop();
        d.pop();
        d
    } else if mutation_kind == 6 {
        // nudge first element up: if < 100, increment
        let mut d = nums;
        if d[0] < 100 {
            d.set(0, d[0] + 1);
        }
        d
    } else if mutation_kind == 7 {
        // nudge first element down: if > 1, decrement
        let mut d = nums;
        if d[0] > 1 {
            d.set(0, d[0] - 1);
        }
        d
    } else if mutation_kind == 8 {
        // set all elements to same value (50)
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
    } else if mutation_kind == 9 {
        // set all freqs to 1 (every even index)
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                i % 2 == 0,
                d.len() == nums.len(),
                2 <= d.len() <= 100,
                d.len() % 2 == 0,
                forall|j: int| 0 <= j < i && j % 2 == 0 ==> d[j] == 1,
                forall|j: int| 0 <= j < i && j % 2 != 0 ==> d[j] == nums[j],
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 1);
            i += 2;
        }
        d
    } else {
        nums // fallback
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
    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
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

fn random_nums(rng: &mut Rng, pair_count: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(pair_count * 2);
    for _ in 0..pair_count {
        nums.push(rng.gen_range_i64(1, 100) as i32); // freq
        nums.push(rng.gen_range_i64(1, 100) as i32); // val
    }
    nums
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= goal { return; }
        let key = format!("{:?}", nums);
        if !seen.insert(key) { return; }
        let output = Solution::decompress_rl_elist(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![1, 2, 3, 4],       // Example 1
        vec![1, 1, 2, 3],       // Example 2
    ];
    for ex in &examples {
        emit(ex.clone(), &mut seen, &mut out, &mut count);
    }

    // Interesting seed inputs
    let seeds: Vec<Vec<i32>> = vec![
        vec![1, 1],                           // minimal: single pair
        vec![100, 100],                       // max freq and val
        vec![1, 100],                         // freq=1, val=100
        vec![100, 1],                         // freq=100, val=1
        vec![1, 1, 1, 1],                     // all ones
        vec![50, 50, 50, 50],                 // mid-range
        vec![1, 1, 1, 2, 1, 3, 1, 4, 1, 5],  // all freq=1
        vec![2, 1, 2, 2, 2, 3],               // all freq=2
        vec![1, 99, 1, 100],                  // near-max vals
        vec![99, 1, 1, 1],                    // near-max freq
    ];

    let mutation_kinds: Vec<u8> = (0..=9).collect();

    // Apply every mutation to every seed
    for s in &seeds {
        for &mk in &mutation_kinds {
            emit(mutate(s.clone(), mk), &mut seen, &mut out, &mut count);
        }
    }

    // Diverse size classes with random mutations
    for i in 0..60 {
        if count >= goal { break; }
        let pair_count = match i % 5 {
            0 => 1,                                     // minimal (2 elements)
            1 => rng.gen_range_usize(1, 3),              // tiny (2-6 elements)
            2 => rng.gen_range_usize(2, 10),             // small (4-20 elements)
            3 => rng.gen_range_usize(11, 25),            // medium (22-50 elements)
            _ => rng.gen_range_usize(26, 50),            // large (52-100 elements)
        };
        let nums = random_nums(&mut rng, pair_count);
        let mk = rng.gen_range_usize(0, 9) as u8;
        emit(mutate(nums, mk), &mut seen, &mut out, &mut count);
    }

    // Fill remaining with random inputs
    while count < goal {
        let pair_count = rng.gen_range_usize(1, 50);
        let nums = random_nums(&mut rng, pair_count);
        emit(mutate(nums, 0), &mut seen, &mut out, &mut count);
    }
}
