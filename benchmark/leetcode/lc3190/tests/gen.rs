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
        // set all elements to multiples of 3
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 50,
                forall|j: int| 0 <= j < i ==> d[j] == 3,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
                forall|j: int| 0 <= j < i ==> 1 <= #[trigger] d[j] <= 50,
                forall|j: int| i <= j < d.len() ==> 1 <= #[trigger] d[j] <= 50,
            decreases d.len() - i,
        {
            d.set(i, 3);
            i += 1;
        }
        d
    } else if mutation_kind == 2 {
        // set all elements to non-multiples of 3 (remainder 1)
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 50,
                forall|j: int| 0 <= j < i ==> d[j] == 1,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
                forall|j: int| 0 <= j < i ==> 1 <= #[trigger] d[j] <= 50,
                forall|j: int| i <= j < d.len() ==> 1 <= #[trigger] d[j] <= 50,
            decreases d.len() - i,
        {
            d.set(i, 1);
            i += 1;
        }
        d
    } else if mutation_kind == 3 {
        // set all elements to non-multiples of 3 (remainder 2)
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 50,
                forall|j: int| 0 <= j < i ==> d[j] == 2,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
                forall|j: int| 0 <= j < i ==> 1 <= #[trigger] d[j] <= 50,
                forall|j: int| i <= j < d.len() ==> 1 <= #[trigger] d[j] <= 50,
            decreases d.len() - i,
        {
            d.set(i, 2);
            i += 1;
        }
        d
    } else if mutation_kind == 4 {
        // set last element to 3 (divisible by 3)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 3);
        d
    } else if mutation_kind == 5 {
        // set first element to 50 (max boundary, remainder 2)
        let mut d = nums;
        d.set(0, 50);
        d
    } else if mutation_kind == 6 {
        // set first element to 1 (min boundary, remainder 1)
        let mut d = nums;
        d.set(0, 1);
        d
    } else if mutation_kind == 7 && nums.len() < 50 {
        // grow by one element
        let mut d = nums;
        d.push(3);
        d
    } else if mutation_kind == 8 && nums.len() > 1 {
        // shrink by one element
        let mut d = nums;
        d.pop();
        d
    } else if mutation_kind == 9 {
        // nudge first element: if < 50, increment
        let mut d = nums;
        if d[0] < 50 {
            d.set(0, d[0] + 1);
        }
        d
    } else if mutation_kind == 10 {
        // nudge first element: if > 1, decrement
        let mut d = nums;
        if d[0] > 1 {
            d.set(0, d[0] - 1);
        }
        d
    } else if mutation_kind == 11 {
        // set last element to 48 (large multiple of 3)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 48);
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
}

struct Solution;
include!("../code.rs");

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(1, 50) as i32);
    }
    nums
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
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
        let output = Solution::minimum_operations(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![1, 2, 3, 4],
        vec![3, 6, 9],
    ];
    for ex in examples {
        emit(ex, &mut seen, &mut out, &mut count);
    }

    // Seed pool: various interesting arrays
    let seeds: Vec<Vec<i32>> = vec![
        vec![1],
        vec![3],
        vec![50],
        vec![49],
        vec![48],
        vec![1, 2],
        vec![3, 6],
        vec![1, 1, 1],
        vec![3, 3, 3],
        vec![2, 2, 2],
        vec![1, 3, 5, 7, 9],
        vec![6, 12, 18, 24, 30],
        vec![50, 49, 48, 47, 46],
        vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
    ];

    let mutation_kinds: Vec<u8> = (0..=11).collect();

    // Apply every mutation to every seed
    for s in &seeds {
        for &mk in &mutation_kinds {
            let result = generate_test_case(s.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Size-class random arrays with random mutations
    for i in 0..60 {
        let len = match i % 5 {
            0 => rng.gen_range_usize(1, 3),       // tiny
            1 => rng.gen_range_usize(1, 10),      // small
            2 => rng.gen_range_usize(11, 25),     // medium
            3 => rng.gen_range_usize(26, 40),     // large
            _ => rng.gen_range_usize(41, 50),     // max
        };
        let s = random_nums(&mut rng, len);
        let mk = rng.gen_range_usize(0, 11) as u8;
        let result = generate_test_case(s, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }

    // Fill remaining with identity-mutated random arrays
    while count < target {
        let len = rng.gen_range_usize(1, 50);
        let s = random_nums(&mut rng, len);
        emit(generate_test_case(s, 0), &mut seen, &mut out, &mut count);
    }
}
