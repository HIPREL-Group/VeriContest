use vstd::prelude::*;

verus! {

pub open spec fn digit_count(n: int) -> int
    decreases n,
{
    if n <= 0 { 1 } else if n < 10 { 1 } else { 1 + digit_count(n / 10) }
}
fn digit_width(n: i32) -> (result: u32)
    requires 1 <= n <= 999999999,
    ensures result == digit_count(n as int), 1 <= result <= n,
    decreases n,
{
    if n < 10 { 1 } else { 1 + digit_width(n / 10) }
}
pub fn generate_test_case(raw: Vec<i32>) -> (result: Vec<i32>)
    ensures 2 <= result.len() <= 100000,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] < 1000000000,
        forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result.len() ==>
            digit_count(#[trigger] result[i] as int) == digit_count(#[trigger] result[j] as int),
{
    let n = if raw.len() < 2 { 2usize } else if raw.len() > 100000 { 100000usize } else { raw.len() };
    let first = if raw.len() == 0 { 1 } else { raw[0] };
    let first = if first < 1 { 1 } else if first > 999999999 { 999999999 } else { first };
    let width = digit_width(first);
    let mut result = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant i <= n, 2 <= n <= 100000, result.len() == i,
            1 <= first <= 999999999, width == digit_count(first as int),
            forall|j: int| 0 <= j < result.len() ==> 1 <= #[trigger] result[j] < 1000000000,
            forall|j: int| 0 <= j < result.len() ==> digit_count(#[trigger] result[j] as int) == width,
        decreases n - i,
    {
        let v = if i < raw.len() { raw[i] } else { first };
        let v = if v < 1 { 1 } else if v > 999999999 { 999999999 } else { v };
        let v = if digit_width(v) == width { v } else { first };
        result.push(v);
        i += 1;
    }
    result
}


pub fn generate_candidate(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        2 <= nums.len() <= 100000,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] < 1_000_000_000,
    ensures
        2 <= result.len() <= 100000,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] < 1_000_000_000,
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
        // set last element to 999_999_999 (max boundary)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 999_999_999);
        d
    } else if mutation_kind == 3 {
        // set all elements to 1
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                2 <= d.len() <= 100000,
                forall|j: int| 0 <= j < i ==> d[j] == 1i32,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 1);
            i += 1;
        }
        d
    } else if mutation_kind == 4 && nums.len() < 100000 {
        // grow by one element
        let mut d = nums;
        d.push(1);
        d
    } else if mutation_kind == 5 && nums.len() > 2 {
        // shrink by one element
        let mut d = nums;
        d.pop();
        d
    } else if mutation_kind == 6 {
        // nudge first element up (if possible)
        let mut d = nums;
        if d[0] < 999_999_998 {
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
    } else if mutation_kind == 8 {
        // set all elements to 999_999_999
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                2 <= d.len() <= 100000,
                forall|j: int| 0 <= j < i ==> d[j] == 999_999_999i32,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 999_999_999);
            i += 1;
        }
        d
    } else if mutation_kind == 9 {
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
    generate_candidate(nums, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_nums(rng: &mut Rng, len: usize, digit_count: usize) -> Vec<i32> {
    let lo: i64 = if digit_count == 1 { 1 } else {
        let mut v: i64 = 1;
        for _ in 1..digit_count { v *= 10; }
        v
    };
    let hi: i64 = {
        let mut v: i64 = 1;
        for _ in 0..digit_count { v *= 10; }
        (v - 1).min(999_999_999)
    };
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(lo, hi) as i32);
    }
    nums
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(3153);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        let nums = generate_test_case(nums);
        if *count >= target { return; }
        let key = format!("{:?}", nums);
        if !seen.insert(key) { return; }
        let output = Solution::sum_digit_differences(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Example test cases from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![13, 23, 12],
        vec![10, 10, 10, 10],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    // Apply every mutation to examples
    for seed_nums in &examples {
        for &mk in &mutation_kinds {
            let result = mutate(seed_nums.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Seed arrays with specific patterns
    let special_seeds: Vec<Vec<i32>> = vec![
        vec![1, 1],                         // minimum length, minimum values
        vec![999_999_999, 999_999_999],     // max values
        vec![1, 999_999_999],               // mix min/max
        vec![100, 200, 300],                // uniform digit count
        vec![5, 5, 5, 5, 5],               // all same
        vec![1, 2, 3, 4, 5, 6, 7, 8, 9],   // sequential single digits
    ];

    for seed_nums in &special_seeds {
        for &mk in &mutation_kinds {
            let result = mutate(seed_nums.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds across size classes with varying digit counts
    for i in 0..80 {
        if count >= target { break; }
        let n: usize = match i % 5 {
            0 => rng.gen_range_usize(2, 5),       // tiny
            1 => rng.gen_range_usize(2, 10),      // small
            2 => rng.gen_range_usize(11, 100),    // medium
            3 => rng.gen_range_usize(101, 1000),  // large
            _ => rng.gen_range_usize(1001, 5000), // very large
        };
        let digit_count = rng.gen_range_usize(1, 9);
        let seed_nums = random_nums(&mut rng, n, digit_count);
        let mk = rng.gen_range_usize(0, 9) as u8;
        let result = mutate(seed_nums, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }

    // Fill remaining with random identity mutations
    while count < target {
        let n = rng.gen_range_usize(2, 500);
        let digit_count = rng.gen_range_usize(1, 9);
        let seed_nums = random_nums(&mut rng, n, digit_count);
        emit(mutate(seed_nums, 0), &mut seen, &mut out, &mut count);
    }
}
