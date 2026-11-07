use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= nums.len() <= 500,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100000,
    ensures
        1 <= result.len() <= 500,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 100000,
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
        // set last element to 100000 (max boundary)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 100000);
        d
    } else if mutation_kind == 3 {
        // set last element to 10 (even-digit number, 2 digits)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 10);
        d
    } else if mutation_kind == 4 {
        // set last element to 1000 (even-digit number, 4 digits)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 1000);
        d
    } else if mutation_kind == 5 {
        // set last element to 5 (odd-digit number, 1 digit)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 5);
        d
    } else if mutation_kind == 6 {
        // set last element to 100 (odd-digit number, 3 digits)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 100);
        d
    } else if mutation_kind == 7 {
        // set last element to 10000 (odd-digit number, 5 digits)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 10000);
        d
    } else if mutation_kind == 8 && nums.len() < 500 {
        // grow: push element 1
        let mut d = nums;
        d.push(1);
        d
    } else if mutation_kind == 9 && nums.len() > 1 {
        // shrink: pop last element
        let mut d = nums;
        d.pop();
        d
    } else if mutation_kind == 10 {
        // nudge last element up (if < 100000)
        let mut d = nums;
        let last = d.len() - 1;
        if d[last] < 100000 {
            d.set(last, d[last] + 1);
        }
        d
    } else if mutation_kind == 11 {
        // nudge last element down (if > 1)
        let mut d = nums;
        let last = d.len() - 1;
        if d[last] > 1 {
            d.set(last, d[last] - 1);
        }
        d
    } else if mutation_kind == 12 {
        // set all elements to 99 (all even-digit)
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 500,
                forall|j: int| 0 <= j < i ==> d[j] == 99,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 99);
            i += 1;
        }
        d
    } else if mutation_kind == 13 {
        // set all elements to 7 (all odd-digit)
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 500,
                forall|j: int| 0 <= j < i ==> d[j] == 7,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 7);
            i += 1;
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

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(1, 100000) as i32);
    }
    nums
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1295);
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
        let output = Solution::find_numbers(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let example_seeds: Vec<Vec<i32>> = vec![
        vec![12, 345, 2, 6, 7896],
        vec![555, 901, 482, 1771],
    ];
    for seed_nums in &example_seeds {
        emit(seed_nums.clone(), &mut seen, &mut out, &mut count);
    }

    // Hand-crafted seeds covering digit-count boundaries
    let crafted_seeds: Vec<Vec<i32>> = vec![
        vec![1],                              // single odd-digit
        vec![10],                             // single even-digit
        vec![99],                             // 2-digit max
        vec![100],                            // 3-digit min
        vec![999],                            // 3-digit max
        vec![1000],                           // 4-digit min
        vec![9999],                           // 4-digit max
        vec![10000],                          // 5-digit min
        vec![99999],                          // 5-digit max
        vec![100000],                         // 6-digit (max value, even digits)
        vec![1, 10, 100, 1000, 10000, 100000], // one of each digit count
        vec![9, 99, 999, 9999, 99999, 100000], // max of each digit count
    ];

    let mutation_kinds: Vec<u8> = (0..=13).collect();

    // Apply every mutation to crafted seeds
    for s in &crafted_seeds {
        for &mk in &mutation_kinds {
            let result = generate_test_case(s.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds with random mutations across size classes
    while count < target {
        let len = match count % 5 {
            0 => rng.gen_range_usize(1, 5),       // tiny
            1 => rng.gen_range_usize(1, 10),      // small
            2 => rng.gen_range_usize(11, 50),     // medium
            3 => rng.gen_range_usize(51, 200),    // large
            _ => rng.gen_range_usize(201, 500),   // max
        };
        let nums = random_nums(&mut rng, len);
        let mk = rng.gen_range_usize(0, 13) as u8;
        let result = generate_test_case(nums, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }
}
