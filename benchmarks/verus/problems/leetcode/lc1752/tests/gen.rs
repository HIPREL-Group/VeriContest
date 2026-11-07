use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= nums.len() <= 100,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
    ensures
        1 <= result.len() <= 100,
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
        // set all elements to the same value (always sorted-and-rotated)
        let mut d = nums;
        let val = d[0];
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 100,
                1 <= val <= 100,
                forall|j: int| 0 <= j < i ==> d[j] == val,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
                forall|j: int| i <= j < d.len() ==> 1 <= #[trigger] d[j] <= 100,
            decreases d.len() - i,
        {
            d.set(i, val);
            i += 1;
        }
        d
    } else if mutation_kind == 4 && nums.len() < 100 {
        // grow by one element (push 1)
        let mut d = nums;
        d.push(1);
        d
    } else if mutation_kind == 5 && nums.len() > 1 {
        // shrink by one element (pop)
        let mut d = nums;
        d.pop();
        d
    } else if mutation_kind == 6 {
        // nudge last element up: if < 100, increment
        let mut d = nums;
        let last = d.len() - 1;
        if d[last] < 100 {
            d.set(last, d[last] + 1);
        }
        d
    } else if mutation_kind == 7 {
        // nudge last element down: if > 1, decrement
        let mut d = nums;
        let last = d.len() - 1;
        if d[last] > 1 {
            d.set(last, d[last] - 1);
        }
        d
    } else if mutation_kind == 8 && nums.len() >= 2 {
        // swap first and last elements
        let mut d = nums;
        let last = d.len() - 1;
        let first_val = d[0];
        let last_val = d[last];
        d.set(0, last_val);
        d.set(last, first_val);
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

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(1, 100) as i32);
    }
    nums
}

fn sorted_rotated_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums: Vec<i32> = (0..len).map(|_| rng.gen_range_i64(1, 100) as i32).collect();
    nums.sort();
    let rot = rng.gen_range_usize(0, len - 1);
    nums.rotate_left(rot);
    nums
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1752);
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
        let output = Solution::check(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![3, 4, 5, 1, 2],   // true
        vec![2, 1, 3, 4],       // false
        vec![1, 2, 3],          // true
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8];

    // Emit examples with all mutations
    for ex in &examples {
        for &mk in &mutation_kinds {
            emit(mutate(ex.clone(), mk), &mut seen, &mut out, &mut count);
        }
    }

    // Hand-crafted edge-case seeds
    let edge_seeds: Vec<Vec<i32>> = vec![
        vec![1],                         // single element
        vec![1, 1],                      // all same, len 2
        vec![100, 100, 100],             // all same max
        vec![1, 2, 3, 4, 5],            // sorted, no rotation
        vec![5, 1, 2, 3, 4],            // sorted, rotated by 1
        vec![2, 3, 4, 5, 1],            // sorted, rotated by 4
        vec![5, 4, 3, 2, 1],            // reverse sorted (false)
        vec![3, 1, 2, 5, 4],            // multiple descents (false)
        vec![1, 1, 1, 1, 1],            // all ones
        vec![100],                       // single max
        vec![50, 50, 50, 50],           // duplicates
        vec![1, 100],                    // two elements sorted
        vec![100, 1],                    // two elements rotated
    ];

    for seed in &edge_seeds {
        for &mk in &mutation_kinds {
            emit(mutate(seed.clone(), mk), &mut seen, &mut out, &mut count);
        }
    }

    // Sorted-and-rotated arrays (should yield true)
    for _ in 0..20 {
        let len = match rng.gen_range_usize(0, 4) {
            0 => 1,
            1 => rng.gen_range_usize(2, 5),
            2 => rng.gen_range_usize(6, 20),
            3 => rng.gen_range_usize(21, 50),
            _ => rng.gen_range_usize(51, 100),
        };
        let nums = sorted_rotated_nums(&mut rng, len);
        let mk = rng.gen_range_usize(0, 8) as u8;
        emit(mutate(nums, mk), &mut seen, &mut out, &mut count);
    }

    // Random arrays (diverse sizes)
    for _ in 0..40 {
        let len = match rng.gen_range_usize(0, 4) {
            0 => 1,
            1 => rng.gen_range_usize(2, 5),
            2 => rng.gen_range_usize(6, 20),
            3 => rng.gen_range_usize(21, 50),
            _ => rng.gen_range_usize(51, 100),
        };
        let nums = random_nums(&mut rng, len);
        let mk = rng.gen_range_usize(0, 8) as u8;
        emit(mutate(nums, mk), &mut seen, &mut out, &mut count);
    }

    // Fill remaining with random arrays, identity mutation
    while count < target {
        let len = rng.gen_range_usize(1, 100);
        let nums = random_nums(&mut rng, len);
        emit(mutate(nums, 0), &mut seen, &mut out, &mut count);
    }
}
