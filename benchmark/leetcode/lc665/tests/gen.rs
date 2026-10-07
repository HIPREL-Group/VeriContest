use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= nums.len() <= 10_000,
        forall|i: int| 0 <= i < nums.len() ==> -100_000 <= #[trigger] nums[i] <= 100_000,
    ensures
        1 <= result.len() <= 10_000,
        forall|i: int| 0 <= i < result.len() ==> -100_000 <= #[trigger] result[i] <= 100_000,
{
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 && nums.len() >= 2 {
        // introduce a single descent at index 0: set nums[0] = nums[1] + 1
        let mut d = nums;
        let v = d[1];
        if v < 100_000 {
            d.set(0, v + 1);
        }
        d
    } else if mutation_kind == 2 && nums.len() >= 2 {
        // make sorted (non-decreasing): set each element to max so far
        let mut d = nums;
        let mut i: usize = 1;
        while i < d.len()
            invariant
                1 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 10_000,
                forall|j: int| 0 <= j < d.len() ==> -100_000 <= #[trigger] d[j] <= 100_000,
            decreases d.len() - i,
        {
            if d[i] < d[i - 1] {
                d.set(i, d[i - 1]);
            }
            i += 1;
        }
        d
    } else if mutation_kind == 3 && nums.len() >= 3 {
        // introduce descent at middle index
        let mid = nums.len() / 2;
        let mut d = nums;
        d.set(mid, -100_000);
        d
    } else if mutation_kind == 4 && nums.len() >= 2 {
        // introduce descent at last pair: set last to -100_000
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, -100_000);
        d
    } else if mutation_kind == 5 {
        // set all elements to same value (trivially non-decreasing)
        let mut d = nums;
        let val = d[0];
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 10_000,
                -100_000 <= val <= 100_000,
                forall|j: int| 0 <= j < i ==> d[j] == val,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
                forall|j: int| 0 <= j < d.len() ==> -100_000 <= #[trigger] d[j] <= 100_000,
            decreases d.len() - i,
        {
            d.set(i, val);
            i += 1;
        }
        d
    } else if mutation_kind == 6 && nums.len() < 10_000 {
        // grow: append 100_000 (largest value)
        let mut d = nums;
        d.push(100_000);
        d
    } else if mutation_kind == 7 && nums.len() > 1 {
        // shrink: remove last element
        let mut d = nums;
        d.pop();
        d
    } else if mutation_kind == 8 {
        // set first element to 100_000 (likely creates descent if len > 1)
        let mut d = nums;
        d.set(0, 100_000);
        d
    } else if mutation_kind == 9 {
        // set all to 0
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 10_000,
                forall|j: int| 0 <= j < i ==> d[j] == 0i32,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
                forall|j: int| 0 <= j < d.len() ==> -100_000 <= #[trigger] d[j] <= 100_000,
            decreases d.len() - i,
        {
            d.set(i, 0);
            i += 1;
        }
        d
    } else if mutation_kind == 10 && nums.len() >= 2 {
        // swap first two elements (may create or fix descent)
        let mut d = nums;
        let a = d[0];
        let b = d[1];
        d.set(0, b);
        d.set(1, a);
        d
    } else if mutation_kind == 11 && nums.len() >= 2 {
        // create two descents (unfixable): set indices 0 and len/2 high
        let mut d = nums;
        d.set(0, 100_000);
        let mid = d.len() / 2;
        if mid > 0 {
            d.set(mid, 100_000);
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

fn random_array(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(-100_000, 100_000) as i32);
    }
    nums
}

fn sorted_array(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    let mut cur = rng.gen_range_i64(-100_000, -50_000) as i32;
    for _ in 0..len {
        nums.push(cur);
        let step = rng.gen_range_i64(0, 10) as i32;
        if cur <= 100_000 - step {
            cur += step;
        }
    }
    nums
}

fn almost_sorted_array(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = sorted_array(rng, len);
    if len >= 2 {
        let idx = rng.gen_range_usize(0, len - 1);
        nums[idx] = rng.gen_range_i64(-100_000, 100_000) as i32;
    }
    nums
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(665);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut emitted = 0usize;

    let mut emit = |nums: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, emitted: &mut usize| {
        if *emitted >= count { return; }
        let key = format!("{:?}", nums);
        if !seen.insert(key) { return; }
        let output = Solution::check_possibility(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *emitted += 1;
    };

    // Example test cases from description
    let examples: Vec<Vec<i32>> = vec![
        vec![4, 2, 3],
        vec![4, 2, 1],
    ];
    for ex in examples {
        emit(ex, &mut seen, &mut out, &mut emitted);
    }

    // Curated seeds: edge cases
    let seeds: Vec<Vec<i32>> = vec![
        vec![1],
        vec![1, 2],
        vec![2, 1],
        vec![1, 2, 3],
        vec![3, 2, 1],
        vec![1, 1, 1],
        vec![1, 3, 2],
        vec![1, 5, 3, 4],
        vec![5, 1, 3, 2],
        vec![1, 2, 3, 4, 5],
        vec![5, 4, 3, 2, 1],
        vec![1, 2, 5, 3, 4],
        vec![-100_000, 100_000],
        vec![100_000, -100_000],
        vec![0, 0, 0, 0],
        vec![1, 2, 3, 2, 5],
        vec![3, 4, 2, 3],
    ];

    let mutation_kinds: Vec<u8> = (0..=11).collect();

    // Apply every mutation to every curated seed
    for s in &seeds {
        for &mk in &mutation_kinds {
            emit(mutate(s.clone(), mk), &mut seen, &mut out, &mut emitted);
        }
    }

    // Random arrays with random mutations
    for _ in 0..200 {
        if emitted >= count { break; }
        let len = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 3),       // tiny
            1 => rng.gen_range_usize(1, 10),       // small
            2 => rng.gen_range_usize(11, 100),     // medium
            3 => rng.gen_range_usize(101, 1000),   // large
            _ => rng.gen_range_usize(1001, 5000),  // max-ish
        };
        let arr = random_array(&mut rng, len);
        let mk = rng.gen_range_usize(0, 11) as u8;
        emit(mutate(arr, mk), &mut seen, &mut out, &mut emitted);
    }

    // Sorted arrays with mutations (test "almost sorted" cases)
    for _ in 0..100 {
        if emitted >= count { break; }
        let len = rng.gen_range_usize(2, 200);
        let arr = sorted_array(&mut rng, len);
        let mk = rng.gen_range_usize(0, 11) as u8;
        emit(mutate(arr, mk), &mut seen, &mut out, &mut emitted);
    }

    // Almost-sorted arrays (one random element changed)
    for _ in 0..100 {
        if emitted >= count { break; }
        let len = rng.gen_range_usize(2, 200);
        let arr = almost_sorted_array(&mut rng, len);
        emit(mutate(arr, 0), &mut seen, &mut out, &mut emitted);
    }

    // Fill remaining with random identity
    while emitted < count {
        let len = rng.gen_range_usize(1, 500);
        let arr = random_array(&mut rng, len);
        emit(mutate(arr, 0), &mut seen, &mut out, &mut emitted);
    }
}
