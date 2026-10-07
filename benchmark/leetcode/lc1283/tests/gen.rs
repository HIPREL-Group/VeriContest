use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    nums: Vec<i32>,
    threshold: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= nums.len() <= 50_000,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000,
        nums.len() <= threshold <= 1_000_000,
    ensures
        1 <= result.0.len() <= 50_000,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 1_000_000,
        result.0.len() <= result.1 <= 1_000_000,
{
    if mutation_kind == 0 {
        // identity
        (nums, threshold)
    } else if mutation_kind == 1 {
        // set last element to 1 (min value)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 1);
        (d, threshold)
    } else if mutation_kind == 2 {
        // set last element to 1_000_000 (max value)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 1_000_000);
        (d, threshold)
    } else if mutation_kind == 3 {
        // set all elements to 1
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 50_000,
                forall|j: int| 0 <= j < i ==> d[j] == 1i32,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
                forall|j: int| 0 <= j < d.len() ==> 1 <= #[trigger] d[j] <= 1_000_000,
            decreases d.len() - i,
        {
            d.set(i, 1);
            i += 1;
        }
        (d, threshold)
    } else if mutation_kind == 4 {
        // set all elements to 1_000_000
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 50_000,
                forall|j: int| 0 <= j < i ==> d[j] == 1_000_000i32,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
                forall|j: int| 0 <= j < d.len() ==> 1 <= #[trigger] d[j] <= 1_000_000,
            decreases d.len() - i,
        {
            d.set(i, 1_000_000);
            i += 1;
        }
        (d, threshold)
    } else if mutation_kind == 5 && nums.len() < 50_000 && (threshold as u64) > (nums.len() as u64) {
        // grow: push element 1
        let mut d = nums;
        d.push(1);
        (d, threshold)
    } else if mutation_kind == 6 && nums.len() > 1 {
        // shrink: pop last element
        let mut d = nums;
        d.pop();
        (d, threshold)
    } else if mutation_kind == 7 {
        // set threshold to nums.len() (minimum valid threshold)
        let t = nums.len() as i32;
        (nums, t)
    } else if mutation_kind == 8 {
        // set threshold to 1_000_000 (maximum valid threshold)
        (nums, 1_000_000)
    } else if mutation_kind == 9 {
        // nudge first element: if > 1, decrement by 1
        let mut d = nums;
        if d[0] > 1 {
            d.set(0, d[0] - 1);
        }
        (d, threshold)
    } else if mutation_kind == 10 {
        // nudge first element: if < 1_000_000, increment by 1
        let mut d = nums;
        if d[0] < 1_000_000 {
            d.set(0, d[0] + 1);
        }
        (d, threshold)
    } else {
        // fallback
        (nums, threshold)
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

extern crate serde_json;
use serde_json::json;

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(1, 1_000_000) as i32);
    }
    nums
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1283);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>, threshold: i32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count {
            return;
        }
        let key = format!("{:?}:{}", nums, threshold);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::smallest_divisor(nums.clone(), threshold);
        writeln!(out, "{}", json!({
            "input": {"nums": nums, "threshold": threshold},
            "output": output
        })).unwrap();
        *count += 1;
    };

    // Example test cases from description.md
    let examples: Vec<(Vec<i32>, i32)> = vec![
        (vec![1, 2, 5, 9], 6),
        (vec![44, 22, 33, 11, 1], 5),
    ];
    for (nums, thr) in examples {
        emit(nums, thr, &mut seen, &mut out, &mut count);
    }

    // Curated seed inputs
    let seed_inputs: Vec<(Vec<i32>, i32)> = vec![
        (vec![1], 1),
        (vec![1], 1_000_000),
        (vec![1_000_000], 1),
        (vec![1_000_000], 1_000_000),
        (vec![1, 1, 1], 3),
        (vec![1_000_000, 1_000_000], 2),
        (vec![500_000], 1),
        (vec![2, 3, 5, 7, 11], 5),
        (vec![100; 10], 10),
        (vec![999_999, 1], 2),
    ];

    let mutation_kinds: Vec<u8> = (0..=10).collect();

    // Apply every mutation to curated seeds
    for (nums, thr) in &seed_inputs {
        for &mk in &mutation_kinds {
            let (result_nums, result_thr) = generate_test_case(nums.clone(), *thr, mk);
            emit(result_nums, result_thr, &mut seen, &mut out, &mut count);
        }
    }

    // Random inputs with diverse size classes and mutations
    while count < target_count {
        let n: usize = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 5),        // tiny
            1 => rng.gen_range_usize(1, 10),        // small
            2 => rng.gen_range_usize(11, 100),       // medium
            3 => rng.gen_range_usize(101, 1000),     // large
            _ => rng.gen_range_usize(1001, 5000),    // very large
        };
        let nums = random_nums(&mut rng, n);
        // threshold in [n, 1_000_000]
        let thr = rng.gen_range_i64(n as i64, 1_000_000) as i32;
        let mk = rng.gen_range_usize(0, 10) as u8;
        let (result_nums, result_thr) = generate_test_case(nums, thr, mk);
        emit(result_nums, result_thr, &mut seen, &mut out, &mut count);
    }
}
