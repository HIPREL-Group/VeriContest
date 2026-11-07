use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= nums.len() <= 50,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 50,
    ensures
        1 <= result.len() <= 50,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 50,
{
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 {
        // set first element to 1 (min boundary)
        let mut d = nums;
        d.set(0, 1);
        d
    } else if mutation_kind == 2 {
        // set first element to 50 (max boundary)
        let mut d = nums;
        d.set(0, 50);
        d
    } else if mutation_kind == 3 && nums.len() < 50 {
        // grow by one element (push 1)
        let mut d = nums;
        d.push(1);
        d
    } else if mutation_kind == 4 && nums.len() > 1 {
        // shrink by one (pop last element)
        let mut d = nums;
        d.pop();
        d
    } else if mutation_kind == 5 {
        // set all elements to 1
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 50,
                forall|j: int| 0 <= j < i ==> #[trigger] d[j] == 1i32,
                forall|j: int| i as int <= j < d.len() ==> #[trigger] d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 1);
            i += 1;
        }
        d
    } else if mutation_kind == 6 {
        // nudge first element up (if < 50)
        let mut d = nums;
        if d[0] < 50 {
            d.set(0, d[0] + 1);
        }
        d
    } else if mutation_kind == 7 {
        // nudge first element down (if > 1)
        let mut d = nums;
        if d[0] > 1 {
            d.set(0, d[0] - 1);
        }
        d
    } else if mutation_kind == 8 && nums.len() >= 2 {
        // swap first two elements
        let mut d = nums;
        let tmp = d[0];
        d.set(0, d[1]);
        d.set(1, tmp);
        d
    } else if mutation_kind == 9 {
        // make sequential prefix: set elements to 1, 2, 3, ..., len
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 50,
                forall|j: int| 0 <= j < i ==> #[trigger] d[j] == (j + 1) as i32,
                forall|j: int| i as int <= j < d.len() ==> #[trigger] d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, (i + 1) as i32);
            i += 1;
        }
        d
    } else if mutation_kind == 10 {
        // set last element to 1 (min boundary)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 1);
        d
    } else if mutation_kind == 11 {
        // set last element to 50 (max boundary)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 50);
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

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(1, 50) as i32);
    }
    nums
}

fn random_sequential_prefix(rng: &mut Rng, len: usize) -> Vec<i32> {
    // Build an array with a sequential prefix of random length, rest random
    let mut nums = Vec::with_capacity(len);
    let prefix_len = rng.gen_range_usize(1, len);
    let start = rng.gen_range_i64(1, (50 - prefix_len as i64 + 1).max(1)) as i32;
    for i in 0..prefix_len {
        let val = start + i as i32;
        if val >= 1 && val <= 50 {
            nums.push(val);
        } else {
            nums.push(rng.gen_range_i64(1, 50) as i32);
        }
    }
    for _ in prefix_len..len {
        nums.push(rng.gen_range_i64(1, 50) as i32);
    }
    nums
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2996);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count {
            return;
        }
        let key = format!("{:?}", nums);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::missing_integer(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Example test cases from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![1, 2, 3, 2, 5],
        vec![3, 4, 5, 1, 12, 14, 13],
    ];
    for ex in &examples {
        emit(ex.clone(), &mut seen, &mut out, &mut count);
    }

    // Hand-crafted seeds covering interesting cases
    let seeds: Vec<Vec<i32>> = vec![
        vec![1],                          // single element
        vec![50],                         // max single element
        vec![1, 2, 3, 4, 5],             // full sequential prefix
        vec![5, 3, 1, 2, 4],             // non-sequential start
        vec![1, 3, 5, 7, 9],             // odd numbers, prefix length 1
        vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10], // long sequential prefix
        vec![10, 11, 12, 13, 14],         // sequential starting at 10
        vec![1, 1, 1, 1, 1],             // all same
        vec![50, 50, 50],                // all max
        vec![1, 2, 4, 5, 6],             // gap in sequence
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];

    // Apply every mutation to every seed
    for s in &seeds {
        for &mk in &mutation_kinds {
            let result = mutate(s.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random arrays with sequential prefixes and random mutations
    for _ in 0..40 {
        let len = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 3),   // tiny
            1 => rng.gen_range_usize(1, 10),   // small
            2 => rng.gen_range_usize(11, 30),  // medium
            3 => rng.gen_range_usize(31, 50),  // large
            _ => rng.gen_range_usize(1, 50),
        };
        let nums = random_sequential_prefix(&mut rng, len);
        let mk = rng.gen_range_usize(0, 11) as u8;
        let result = mutate(nums, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }

    // Fill remaining with random arrays
    while count < target_count {
        let len = rng.gen_range_usize(1, 50);
        let nums = random_nums(&mut rng, len);
        let mk = rng.gen_range_usize(0, 11) as u8;
        let result = mutate(nums, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }
}
