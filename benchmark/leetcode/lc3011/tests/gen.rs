use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= nums.len() <= 100,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 256,
    ensures
        1 <= result.len() <= 100,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 256,
{
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 {
        // set first element to 1 (min boundary)
        let mut v = nums;
        v.set(0, 1);
        v
    } else if mutation_kind == 2 {
        // set first element to 256 (max boundary)
        let mut v = nums;
        v.set(0, 256);
        v
    } else if mutation_kind == 3 {
        // set last element to 1
        let mut v = nums;
        let last = v.len() - 1;
        v.set(last, 1);
        v
    } else if mutation_kind == 4 {
        // set last element to 256
        let mut v = nums;
        let last = v.len() - 1;
        v.set(last, 256);
        v
    } else if mutation_kind == 5 && nums.len() >= 2 {
        // swap first and last elements
        let mut v = nums;
        let last = v.len() - 1;
        let first_val = v[0];
        let last_val = v[last];
        v.set(0, last_val);
        v.set(last, first_val);
        v
    } else if mutation_kind == 6 {
        // set all elements to 1
        let mut v = nums;
        let mut i: usize = 0;
        while i < v.len()
            invariant
                0 <= i <= v.len(),
                v.len() == nums.len(),
                1 <= v.len() <= 100,
                forall|j: int| 0 <= j < i ==> v[j] == 1i32,
                forall|j: int| i <= j < v.len() ==> v[j] == nums[j],
            decreases v.len() - i,
        {
            v.set(i, 1);
            i += 1;
        }
        v
    } else if mutation_kind == 7 {
        // set all elements to 256
        let mut v = nums;
        let mut i: usize = 0;
        while i < v.len()
            invariant
                0 <= i <= v.len(),
                v.len() == nums.len(),
                1 <= v.len() <= 100,
                forall|j: int| 0 <= j < i ==> v[j] == 256i32,
                forall|j: int| i <= j < v.len() ==> v[j] == nums[j],
            decreases v.len() - i,
        {
            v.set(i, 256);
            i += 1;
        }
        v
    } else if mutation_kind == 8 {
        // nudge first element up if < 256
        let mut v = nums;
        if v[0] < 256 {
            v.set(0, v[0] + 1);
        }
        v
    } else if mutation_kind == 9 {
        // nudge first element down if > 1
        let mut v = nums;
        if v[0] > 1 {
            v.set(0, v[0] - 1);
        }
        v
    } else if mutation_kind == 10 && nums.len() < 100 {
        // append element 128 (grow by one)
        let mut v = nums;
        v.push(128);
        v
    } else if mutation_kind == 11 && nums.len() > 1 {
        // remove last element (shrink by one)
        let mut v = nums;
        v.pop();
        v
    } else {
        nums  // fallback
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
        nums.push(rng.gen_range_i64(1, 256) as i32);
    }
    nums
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut emitted = 0usize;

    let mut emit = |nums: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, emitted: &mut usize| {
        if *emitted >= count {
            return;
        }
        let key = format!("{:?}", nums);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::can_sort_array(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *emitted += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![8, 4, 2, 30, 15],
        vec![1, 2, 3, 4, 5],
        vec![3, 16, 8, 4, 2],
    ];
    for ex in examples {
        emit(ex, &mut seen, &mut out, &mut emitted);
    }

    // Boundary and special cases
    let specials: Vec<Vec<i32>> = vec![
        vec![1],                         // single element, min value
        vec![256],                       // single element, max value
        vec![1, 256],                    // two elements, min and max
        vec![256, 1],                    // two elements, reversed
        vec![1, 1, 1, 1, 1],            // all same (min)
        vec![256, 256, 256],             // all same (max)
        vec![128, 64, 32, 16, 8, 4, 2, 1], // powers of 2 descending (all popcount 1)
        vec![1, 2, 4, 8, 16, 32, 64, 128], // powers of 2 ascending
        vec![3, 5, 6, 9, 10, 12],       // popcount 2 sorted
        vec![7, 11, 13, 14, 19, 21],    // popcount 3 sorted
        vec![15, 23, 27, 29, 30],       // popcount 4 sorted
        vec![1, 3, 7, 15],              // different popcounts ascending
        vec![15, 7, 3, 1],              // different popcounts descending
        vec![255, 127, 63, 31],         // high popcount values descending
    ];
    for sp in specials {
        emit(sp, &mut seen, &mut out, &mut emitted);
    }

    // Seed pool with mutations
    let seed_sizes: Vec<usize> = vec![1, 2, 3, 5, 10, 20, 50, 100];
    let num_mutations: u8 = 12;

    for &sz in &seed_sizes {
        let base = random_nums(&mut rng, sz);
        for mk in 0..num_mutations {
            if emitted >= count { break; }
            let mutated = mutate(base.clone(), mk);
            emit(mutated, &mut seen, &mut out, &mut emitted);
        }
    }

    // Fill remaining with random arrays of diverse sizes
    while emitted < count {
        let sz = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 3),     // tiny
            1 => rng.gen_range_usize(4, 10),     // small
            2 => rng.gen_range_usize(11, 50),    // medium
            3 => rng.gen_range_usize(51, 100),   // large
            _ => rng.gen_range_usize(1, 100),    // any
        };
        let base = random_nums(&mut rng, sz);
        let mk = rng.gen_range_usize(0, num_mutations as usize - 1) as u8;
        let mutated = mutate(base, mk);
        emit(mutated, &mut seen, &mut out, &mut emitted);
    }
}
