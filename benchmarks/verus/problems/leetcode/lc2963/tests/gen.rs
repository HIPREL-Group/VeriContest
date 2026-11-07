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
        // set all elements to the first element (single block, answer = 1)
        let val = nums[0];
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 100_000,
                1 <= val <= 1_000_000_000,
                forall|j: int| 0 <= j < i ==> d[j] == val,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, val);
            i += 1;
        }
        d
    } else if mutation_kind == 2 {
        // set last element equal to first element (forces single block spanning entire array)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, d[0]);
        d
    } else if mutation_kind == 3 && nums.len() > 1 {
        // shrink: remove last element
        let mut d = nums;
        d.pop();
        d
    } else if mutation_kind == 4 && nums.len() < 100_000 {
        // grow: duplicate last element
        let mut d = nums;
        let last = d.len() - 1;
        let v = d[last];
        d.push(v);
        d
    } else if mutation_kind == 5 {
        // set first element to boundary value 1
        let mut d = nums;
        d.set(0, 1);
        d
    } else if mutation_kind == 6 {
        // set first element to boundary value 1_000_000_000
        let mut d = nums;
        d.set(0, 1_000_000_000i32);
        d
    } else if mutation_kind == 7 && nums.len() >= 2 {
        // swap first two elements
        let mut d = nums;
        let a = d[0];
        let b = d[1];
        d.set(0, b);
        d.set(1, a);
        d
    } else if mutation_kind == 8 {
        // nudge first element: if < 1_000_000_000, increment by 1
        let mut d = nums;
        if d[0] < 1_000_000_000i32 {
            d.set(0, d[0] + 1);
        }
        d
    } else if mutation_kind == 9 {
        // nudge first element down: if > 1, decrement by 1
        let mut d = nums;
        if d[0] > 1 {
            d.set(0, d[0] - 1);
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

extern crate serde_json;
use serde_json::json;

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(1, 1_000_000_000) as i32);
    }
    nums
}

fn random_nums_with_repeats(rng: &mut Rng, len: usize) -> Vec<i32> {
    let num_distinct = rng.gen_range_usize(1, len.min(20));
    let mut palette = Vec::with_capacity(num_distinct);
    for _ in 0..num_distinct {
        palette.push(rng.gen_range_i64(1, 1_000_000_000) as i32);
    }
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        let idx = rng.gen_range_usize(0, palette.len() - 1);
        nums.push(palette[idx]);
    }
    nums
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2963);
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
        let output = Solution::number_of_good_partitions(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![1, 2, 3, 4],
        vec![1, 1, 1, 1],
        vec![1, 2, 1, 3],
    ];
    for ex in &examples {
        emit(ex.clone(), &mut seen, &mut out, &mut count);
    }

    // Hand-crafted seeds
    let seeds: Vec<Vec<i32>> = vec![
        vec![1],
        vec![1, 2],
        vec![1, 1],
        vec![1, 2, 3, 2, 1],
        vec![1, 2, 3, 1, 2, 3],
        vec![1, 2, 1, 2, 1, 2],
        vec![1_000_000_000],
        vec![1, 1_000_000_000],
        vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
        vec![5, 5, 5, 5, 5, 5, 5, 5, 5, 5],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    // Apply every mutation to every seed
    for s in &seeds {
        for &mk in &mutation_kinds {
            let result = mutate(s.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random arrays with size classes and mutations
    for i in 0..60 {
        let n: usize = match i % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 1000),
            _ => rng.gen_range_usize(1001, 5000),
        };
        let seed_nums = if i % 2 == 0 {
            random_nums(&mut rng, n)
        } else {
            random_nums_with_repeats(&mut rng, n)
        };
        let mk = rng.gen_range_usize(0, 9) as u8;
        let result = mutate(seed_nums, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }

    // Fill remaining with random arrays (identity mutation)
    while count < target {
        let n = rng.gen_range_usize(1, 1000);
        let seed_nums = random_nums_with_repeats(&mut rng, n);
        emit(mutate(seed_nums, 0), &mut seen, &mut out, &mut count);
    }
}
