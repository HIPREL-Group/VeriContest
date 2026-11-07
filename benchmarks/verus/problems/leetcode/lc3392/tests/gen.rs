use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: Vec<i32>) -> (result: Vec<i32>)
    ensures
        3 <= result.len() <= 100,
        forall|i: int| 0 <= i < result.len() ==> -100 <= #[trigger] result[i] <= 100,
{
    let n = if values.len() < 3 { 3usize }
            else if values.len() > 100 { 100usize } else { values.len() };
    let mut result = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant
            3 <= n <= 100,
            0 <= i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < result.len() ==> -100 <= #[trigger] result[j] <= 100,
        decreases n - i,
    {
        let value = if i < values.len() { values[i] } else { -100 };
        let value = if value < -100 { -100 } else if value > 100 { 100 } else { value };
        result.push(value);
        i += 1;
    }
    result
}


pub fn generate_candidate(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        3 <= nums.len() <= 100,
        forall|i: int| 0 <= i < nums.len() ==> -100 <= #[trigger] nums[i] <= 100,
    ensures
        3 <= result.len() <= 100,
        forall|i: int| 0 <= i < result.len() ==> -100 <= #[trigger] result[i] <= 100,
{
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 {
        // nudge first element up
        let mut d = nums;
        if d[0] < 100 {
            d.set(0, d[0] + 1);
        }
        d
    } else if mutation_kind == 2 {
        // nudge first element down
        let mut d = nums;
        if d[0] > -100 {
            d.set(0, d[0] - 1);
        }
        d
    } else if mutation_kind == 3 {
        // negate first element
        let mut d = nums;
        let v = d[0];
        if v > -100 && v < 100 {
            d.set(0, -v);
        }
        d
    } else if mutation_kind == 4 {
        // set all elements to zero
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                3 <= d.len() <= 100,
                forall|j: int| 0 <= j < i ==> d[j] == 0i32,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 0);
            i += 1;
        }
        d
    } else if mutation_kind == 5 && nums.len() < 100 {
        // grow by one element (push 0)
        let mut d = nums;
        d.push(0);
        d
    } else if mutation_kind == 6 && nums.len() > 3 {
        // shrink by one element (pop)
        let mut d = nums;
        d.pop();
        d
    } else if mutation_kind == 7 {
        // swap first two elements
        let mut d = nums;
        let a = d[0];
        let b = d[1];
        d.set(0, b);
        d.set(1, a);
        d
    } else if mutation_kind == 8 {
        // set last element to boundary 100
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 100);
        d
    } else if mutation_kind == 9 {
        // set last element to boundary -100
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, -100);
        d
    } else if mutation_kind == 10 {
        // set middle element to 0
        let mut d = nums;
        let mid = d.len() / 2;
        d.set(mid, 0);
        d
    } else {
        // fallback
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
    generate_candidate(nums, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(-100, 100) as i32);
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
        let nums = generate_test_case(nums);
        if *count >= target {
            return;
        }
        let key = format!("{:?}", nums);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::count_subarrays(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![1, 2, 1, 4, 1],
        vec![1, 1, 1],
    ];

    // Curated seeds: boundary and interesting cases
    let seeds: Vec<Vec<i32>> = vec![
        vec![0, 0, 0],
        vec![1, 4, 1],             // 1+1 = 2 = 4/2 → match
        vec![100, 100, 100],
        vec![-100, -100, -100],
        vec![100, 0, -100],
        vec![-100, 0, 100],
        vec![0, 0, 0, 0, 0],
        vec![1, 2, 1, 2, 1],
        vec![50, 100, 50],         // 50+50 = 100 = 100/... wait, 2*(50+50) = 200 != 100
        vec![25, 100, 25],         // 2*(25+25) = 100 == 100 → match
        vec![-50, -100, -50],      // 2*(-50+-50) = -200 != -100
        vec![-50, -200, -50],      // would be out of range
        vec![0, 100, 0, 100, 0],
        vec![1, 0, -1],           // 2*(1 + -1) = 0 == 0 → match
        vec![10, 20, 10, 20, 10],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

    // Emit example inputs
    for ex in &examples {
        emit(ex.clone(), &mut seen, &mut out, &mut count);
    }

    // Apply every mutation to every seed
    for seed in &seeds {
        for &mk in &mutation_kinds {
            let result = mutate(seed.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds across size classes with random mutations
    for i in 0..80 {
        let len = match i % 5 {
            0 => rng.gen_range_usize(3, 5),    // tiny
            1 => rng.gen_range_usize(3, 10),   // small
            2 => rng.gen_range_usize(11, 30),  // medium
            3 => rng.gen_range_usize(31, 70),  // large
            _ => rng.gen_range_usize(71, 100), // max
        };
        let seed = random_nums(&mut rng, len);
        let mk = rng.gen_range_usize(0, 10) as u8;
        let result = mutate(seed, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }

    // Fill remaining with random identity
    while count < target {
        let len = rng.gen_range_usize(3, 100);
        let seed = random_nums(&mut rng, len);
        emit(mutate(seed, 0), &mut seen, &mut out, &mut count);
    }
}
