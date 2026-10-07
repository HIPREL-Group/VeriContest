use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        2 <= nums.len() <= 100000,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000000,
    ensures
        2 <= result.len() <= 100000,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 1000000,
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
        // set last element to 1000000 (max boundary)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 1000000);
        d
    } else if mutation_kind == 3 {
        // set all elements to the same value (first element)
        let mut d = nums;
        let val = d[0];
        let mut i: usize = 1;
        while i < d.len()
            invariant
                1 <= i <= d.len(),
                d.len() == nums.len(),
                2 <= d.len() <= 100000,
                1 <= val <= 1000000,
                forall|j: int| 0 <= j < i ==> d[j] == val,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
                forall|j: int| i <= j < d.len() ==> 1 <= #[trigger] d[j] <= 1000000,
            decreases d.len() - i,
        {
            d.set(i, val);
            i += 1;
        }
        d
    } else if mutation_kind == 4 && nums.len() < 100000 {
        // grow by one element (push 1)
        let mut d = nums;
        d.push(1);
        d
    } else if mutation_kind == 5 && nums.len() > 2 {
        // shrink by one element (pop)
        let mut d = nums;
        d.pop();
        d
    } else if mutation_kind == 6 {
        // nudge last element up (if < 1000000)
        let mut d = nums;
        let last = d.len() - 1;
        if d[last] < 1000000 {
            d.set(last, d[last] + 1);
        }
        d
    } else if mutation_kind == 7 {
        // nudge last element down (if > 1)
        let mut d = nums;
        let last = d.len() - 1;
        if d[last] > 1 {
            d.set(last, d[last] - 1);
        }
        d
    } else if mutation_kind == 8 {
        // make consecutive triple: set last 3 elements to val, val+1, val+2
        let mut d = nums;
        if d.len() >= 3 {
            let base = d[0];
            if base <= 999998 {
                let last = d.len() - 1;
                d.set(last - 2, base);
                d.set(last - 1, base + 1);
                d.set(last, base + 2);
            }
        }
        d
    } else if mutation_kind == 9 {
        // make equal pair: set first two elements equal
        let mut d = nums;
        let val = d[0];
        d.set(1, val);
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

fn mutate(nums: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(nums, mutation_kind)
}

struct Solution;
include!("../code.rs");

extern crate serde_json;
use serde_json::json;

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(1, 1000000) as i32);
    }
    nums
}

// Build an array that has a valid partition (pairs of equal elements)
fn valid_partition_array(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::new();
    let mut remaining = len;
    while remaining > 0 {
        let val = rng.gen_range_i64(1, 1000000) as i32;
        if remaining >= 3 && rng.next_u64() % 3 != 0 {
            // triple: 3 equal or 3 consecutive
            if rng.next_u64() % 2 == 0 && val <= 999998 {
                nums.push(val);
                nums.push(val + 1);
                nums.push(val + 2);
            } else {
                nums.push(val);
                nums.push(val);
                nums.push(val);
            }
            remaining -= 3;
        } else if remaining >= 2 {
            nums.push(val);
            nums.push(val);
            remaining -= 2;
        } else {
            // remaining == 1: extend the last group
            let last = *nums.last().unwrap();
            nums.push(last);
            remaining -= 1;
        }
    }
    nums
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2369);
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
        let output = Solution::valid_partition(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Example test cases from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![4, 4, 4, 5, 6],
        vec![1, 1, 1, 2],
    ];
    for ex in examples {
        emit(ex, &mut seen, &mut out, &mut count);
    }

    // Curated seeds: various partition structures
    let seeds: Vec<Vec<i32>> = vec![
        vec![1, 1],
        vec![1, 1, 1],
        vec![1, 2, 3],
        vec![1, 1, 2, 2],
        vec![1, 1, 1, 1, 1, 1],
        vec![1, 2, 3, 4, 5, 6],
        vec![1, 1, 2, 3, 4, 4],
        vec![1000000, 1000000],
        vec![999998, 999999, 1000000],
        vec![1, 1, 1, 2, 3, 4],
        vec![5, 5, 5, 5, 5],
        vec![1, 2, 3, 3, 3],
        vec![7, 7, 8, 8, 9, 9],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    // Apply every mutation to every seed
    for seed in &seeds {
        for &mk in &mutation_kinds {
            let result = mutate(seed.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random arrays with random mutations (diverse sizes)
    let size_classes: Vec<(usize, usize)> = vec![
        (2, 5),
        (6, 20),
        (21, 100),
        (101, 1000),
        (1001, 10000),
    ];
    for &(lo, hi) in &size_classes {
        for _ in 0..5 {
            let len = rng.gen_range_usize(lo, hi);
            let seed = random_nums(&mut rng, len);
            let mk = rng.gen_range_usize(0, 9) as u8;
            let result = mutate(seed, mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Arrays designed to have valid partitions
    for _ in 0..20 {
        let len = rng.gen_range_usize(2, 200);
        let len = if len % 2 == 1 && len < 3 { 2 } else { len };
        let arr = valid_partition_array(&mut rng, len);
        emit(arr, &mut seen, &mut out, &mut count);
    }

    // Fill remaining with random arrays
    while count < target_count {
        let len = rng.gen_range_usize(2, 500);
        let seed = random_nums(&mut rng, len);
        emit(mutate(seed, 0), &mut seen, &mut out, &mut count);
    }
}
