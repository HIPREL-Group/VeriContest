use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= nums.len() <= 100000,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000000000,
    ensures
        1 <= result.len() <= 100000,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 1000000000,
{
    if mutation_kind == 0 {
        nums
    } else if mutation_kind == 1 {
        // set last element to 1 (min boundary)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 1);
        d
    } else if mutation_kind == 2 {
        // set last element to 1_000_000_000 (max boundary)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 1_000_000_000);
        d
    } else if mutation_kind == 3 {
        // set all elements to the same value
        let mut d = nums;
        let val = d[0];
        let mut i: usize = 1;
        while i < d.len()
            invariant
                1 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 100000,
                1 <= val <= 1000000000,
                forall|j: int| 0 <= j < i ==> d[j] == val,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
                forall|j: int| 0 <= j < i ==> 1 <= #[trigger] d[j] <= 1000000000,
                forall|j: int| i <= j < d.len() ==> 1 <= #[trigger] d[j] <= 1000000000,
            decreases d.len() - i,
        {
            d.set(i, val);
            i += 1;
        }
        d
    } else if mutation_kind == 4 && nums.len() < 100000 {
        // grow by one element
        let mut d = nums;
        d.push(1);
        d
    } else if mutation_kind == 5 && nums.len() > 1 {
        // shrink by one element
        let mut d = nums;
        d.pop();
        d
    } else if mutation_kind == 6 && nums.len() >= 2 {
        // swap first and last elements
        let mut d = nums;
        let last = d.len() - 1;
        let first_val = d[0];
        let last_val = d[last];
        d.set(0, last_val);
        d.set(last, first_val);
        d
    } else if mutation_kind == 7 {
        // nudge last element up (if room)
        let mut d = nums;
        let last = d.len() - 1;
        if d[last] < 1_000_000_000 {
            d.set(last, d[last] + 1);
        }
        d
    } else if mutation_kind == 8 {
        // nudge last element down (if room)
        let mut d = nums;
        let last = d.len() - 1;
        if d[last] > 1 {
            d.set(last, d[last] - 1);
        }
        d
    } else if mutation_kind == 9 {
        // set first element to match second element
        if nums.len() >= 2 {
            let mut d = nums;
            let second_val = d[1];
            d.set(0, second_val);
            d
        } else {
            nums
        }
    } else {
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
        let (lo, hi) = if lo <= hi { (lo, hi) } else { (hi, lo) };
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let (lo, hi) = if lo <= hi { (lo, hi) } else { (hi, lo) };
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

struct Solution;
include!("../code.rs");

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(1, 1_000_000_000) as i32);
    }
    nums
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2342);
    let count_target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= count_target {
            return;
        }
        let key = format!("{:?}", nums);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::maximum_sum(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let example_seeds: Vec<Vec<i32>> = vec![
        vec![18, 43, 36, 13, 7],
        vec![10, 12, 19, 14],
    ];

    // Curated seeds: boundary values, same-digit-sum pairs, single elements
    let curated_seeds: Vec<Vec<i32>> = vec![
        vec![1],
        vec![1, 1],
        vec![1, 1000000000],
        vec![999999999, 1000000000],
        vec![1, 2, 3, 4, 5],
        vec![11, 20, 30, 12],
        vec![100, 10, 1],
        vec![99, 99, 99],
        vec![123, 321, 213],
        vec![1, 10, 100, 1000, 10000, 100000, 1000000, 10000000, 100000000, 1000000000],
        vec![999999999, 999999999],
        vec![5, 50, 500],
        vec![19, 28, 37, 46, 55],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    // Emit example inputs with all mutations via generate_test_case
    for seed_nums in &example_seeds {
        for &mk in &mutation_kinds {
            let result = generate_test_case(seed_nums.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Emit curated seeds with all mutations via generate_test_case
    for seed_nums in &curated_seeds {
        for &mk in &mutation_kinds {
            let result = generate_test_case(seed_nums.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds across size classes with random mutations
    let mut _attempts = 0usize;
    while count < count_target {
        _attempts += 1;
        if _attempts > 10000 { break; }
        // Keep sizes small since code.rs is O(n²)
        let n = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(2, 10),
            2 => rng.gen_range_usize(11, 50),
            3 => rng.gen_range_usize(51, 200),
            _ => rng.gen_range_usize(201, 500),
        };
        let seed_nums = random_nums(&mut rng, n);
        let mk = rng.gen_range_usize(0, 9) as u8;
        let result = generate_test_case(seed_nums, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }
}
