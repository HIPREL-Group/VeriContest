use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= nums.len() <= 100_000,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000_000,
    ensures
        1 <= result.len() <= 100_000,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 1_000_000_000,
{
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 {
        // set last element to 1 (forces GCD = 1)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 1);
        d
    } else if mutation_kind == 2 {
        // nudge last element up (if < max)
        let mut d = nums;
        let last = d.len() - 1;
        if d[last] < 1_000_000_000 {
            d.set(last, d[last] + 1);
        }
        d
    } else if mutation_kind == 3 {
        // nudge last element down (if > 1)
        let mut d = nums;
        let last = d.len() - 1;
        if d[last] > 1 {
            d.set(last, d[last] - 1);
        }
        d
    } else if mutation_kind == 4 && nums.len() > 1 {
        // pop last element (shrink)
        let mut d = nums;
        d.pop();
        d
    } else if mutation_kind == 5 && nums.len() < 100_000 {
        // push element 1 (grow, and forces GCD = 1)
        let mut d = nums;
        d.push(1);
        d
    } else if mutation_kind == 6 {
        // set last element to max boundary
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 1_000_000_000);
        d
    } else if mutation_kind == 7 {
        // set last element to min boundary (1)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 1);
        d
    } else if mutation_kind == 8 {
        // set first element to 2 (common factor test)
        let mut d = nums;
        d.set(0, 2);
        d
    } else if mutation_kind == 9 && nums.len() < 100_000 {
        // push element 2 (grow with small prime)
        let mut d = nums;
        d.push(2);
        d
    } else {
        nums // fallback
    }
}

} // verus!

extern crate serde_json;
use serde_json::json;

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
    fn gen_u8(&mut self) -> u8 {
        (self.next_u64() % 256) as u8
    }
}

struct Solution;
include!("../code.rs");

fn random_nums(rng: &mut Rng, len: usize, lo: i64, hi: i64) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(lo, hi) as i32);
    }
    v
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count_target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize, target: usize| {
        if *count >= target { return; }
        let key = format!("{:?}", nums);
        if !seen.insert(key) { return; }
        let output = Solution::is_good_array(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description
    let examples: Vec<Vec<i32>> = vec![
        vec![12, 5, 7, 23],
        vec![29, 6, 10],
        vec![3, 6],
    ];
    for ex in examples {
        emit(ex, &mut seen, &mut out, &mut count, count_target);
    }

    // Interesting seed arrays
    let seeds: Vec<Vec<i32>> = vec![
        vec![1],
        vec![2],
        vec![1_000_000_000],
        vec![2, 3],
        vec![4, 6],
        vec![6, 10, 15],
        vec![2, 4, 8],
        vec![7, 11, 13],
        vec![1, 1_000_000_000],
        vec![2, 3, 5, 7],
        vec![6, 9, 12],
        vec![100, 75, 50],
        vec![999_999_999, 1_000_000_000],
        vec![2, 2, 2, 2],
        vec![3, 3, 3],
    ];

    let mutation_kinds: Vec<u8> = (0..=9).collect();

    // Apply every mutation to every seed
    for s in &seeds {
        for &mk in &mutation_kinds {
            if count >= count_target { break; }
            let result = generate_test_case(s.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count, count_target);
        }
        if count >= count_target { break; }
    }

    // Random arrays with diverse sizes and random mutations
    while count < count_target {
        let n = match count % 5 {
            0 => rng.gen_range_usize(1, 5),        // tiny
            1 => rng.gen_range_usize(1, 10),        // small
            2 => rng.gen_range_usize(11, 100),      // medium
            3 => rng.gen_range_usize(101, 1000),    // large
            _ => rng.gen_range_usize(1001, 10000),  // big
        };

        // Mix value ranges for diversity
        let (lo, hi): (i64, i64) = match count % 4 {
            0 => (1, 100),
            1 => (1, 1_000_000),
            2 => (1, 1_000_000_000),
            _ => (100_000_000, 1_000_000_000),
        };

        let nums = random_nums(&mut rng, n, lo, hi);
        let mk = rng.gen_u8() % 10;
        let result = generate_test_case(nums, mk);
        emit(result, &mut seen, &mut out, &mut count, count_target);
    }
}
