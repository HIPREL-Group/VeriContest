use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= nums.len() <= 10_000,
        forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 100_000,
    ensures
        1 <= result.len() <= 10_000,
        forall|i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] <= 100_000,
{
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 {
        // set first element to 0 (may block early)
        let mut d = nums;
        d.set(0, 0);
        d
    } else if mutation_kind == 2 && nums.len() > 1 {
        // set middle element to 0 (potential trap)
        let mut d = nums;
        let mid = d.len() / 2;
        d.set(mid, 0);
        d
    } else if mutation_kind == 3 {
        // set all elements to 0 (unreachable unless len == 1)
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 10_000,
                forall|j: int| 0 <= j < i ==> d[j] == 0i32,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 0);
            i += 1;
        }
        d
    } else if mutation_kind == 4 && nums.len() < 10_000 {
        // grow by one element (push 0)
        let mut d = nums;
        d.push(0);
        d
    } else if mutation_kind == 5 && nums.len() > 1 {
        // shrink by one element (pop)
        let mut d = nums;
        d.pop();
        d
    } else if mutation_kind == 6 {
        // set first element to large value (easy jump)
        let mut d = nums;
        d.set(0, 100_000);
        d
    } else if mutation_kind == 7 {
        // set last element to 0
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 0);
        d
    } else if mutation_kind == 8 {
        // nudge first element up (if < 100_000)
        let mut d = nums;
        if d[0] < 100_000 {
            d.set(0, d[0] + 1);
        }
        d
    } else if mutation_kind == 9 {
        // nudge first element down (if > 0)
        let mut d = nums;
        if d[0] > 0 {
            d.set(0, d[0] - 1);
        }
        d
    } else if mutation_kind == 10 && nums.len() >= 2 {
        // swap first and last elements
        let mut d = nums;
        let last = d.len() - 1;
        let first_val = d[0];
        let last_val = d[last];
        d.set(0, last_val);
        d.set(last, first_val);
        d
    } else if mutation_kind == 11 {
        // set all elements to 1 (barely reachable)
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 10_000,
                forall|j: int| 0 <= j < i ==> d[j] == 1i32,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 1);
            i += 1;
        }
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

fn random_nums(rng: &mut Rng, len: usize, max_val: i64) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(0, max_val) as i32);
    }
    v
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(55);
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
        let output = Solution::can_jump(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![2, 3, 1, 1, 4],  // true
        vec![3, 2, 1, 0, 4],  // false
    ];

    // Hand-crafted seeds covering edge cases
    let seeds: Vec<Vec<i32>> = vec![
        vec![0],                          // single element, trivially true
        vec![1],                          // single element
        vec![1, 0],                       // barely reachable
        vec![0, 1],                       // blocked at start
        vec![1, 1, 1, 1, 1],             // step-by-step
        vec![5, 0, 0, 0, 0, 0],          // big jump
        vec![1, 0, 0],                    // blocked mid
        vec![2, 0, 0],                    // just reaches end
        vec![0, 0, 0, 0],                // all zeros, blocked
        vec![100_000],                    // max value single
        vec![1, 2, 3, 4, 5],             // increasing
        vec![5, 4, 3, 2, 1, 0],          // decreasing
        vec![3, 0, 0, 0],                // exact reach
        vec![2, 0, 0, 0],                // can't quite reach
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];

    // Emit examples with identity mutation first
    for ex in &examples {
        emit(mutate(ex.clone(), 0), &mut seen, &mut out, &mut count);
    }

    // Apply every mutation to every seed
    for s in &seeds {
        for &mk in &mutation_kinds {
            emit(mutate(s.clone(), mk), &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds across diverse size classes with random mutations
    for i in 0..80 {
        if count >= target { break; }
        let n: usize = match i % 5 {
            0 => rng.gen_range_usize(1, 5),         // tiny
            1 => rng.gen_range_usize(1, 10),        // small
            2 => rng.gen_range_usize(11, 100),      // medium
            3 => rng.gen_range_usize(101, 1000),    // large
            _ => rng.gen_range_usize(1001, 10_000), // max
        };
        // Mix value ranges: mostly small jumps, occasionally large
        let max_val: i64 = if i % 4 == 0 { 100_000 } else if i % 4 == 1 { (n as i64).max(1) } else if i % 4 == 2 { 5 } else { 1 };
        let nums = random_nums(&mut rng, n, max_val);
        let mk = rng.gen_range_usize(0, 11) as u8;
        emit(mutate(nums, mk), &mut seen, &mut out, &mut count);
    }

    // Fill remaining with random identity
    while count < target {
        let n = rng.gen_range_usize(1, 10_000);
        let max_val: i64 = if count % 3 == 0 { 100_000 } else { 5 };
        let nums = random_nums(&mut rng, n, max_val);
        emit(mutate(nums, 0), &mut seen, &mut out, &mut count);
    }
}
