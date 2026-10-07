use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= nums.len() <= 100_000,
        forall|i: int| 0 <= i < nums.len() ==> (#[trigger] nums[i] == 0 || nums[i] == 1),
    ensures
        1 <= result.len() <= 100_000,
        forall|i: int| 0 <= i < result.len() ==> (#[trigger] result[i] == 0 || result[i] == 1),
{
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 {
        // set last element to 0
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 0);
        d
    } else if mutation_kind == 2 {
        // set last element to 1
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 1);
        d
    } else if mutation_kind == 3 {
        // set first element to 0
        let mut d = nums;
        d.set(0, 0);
        d
    } else if mutation_kind == 4 {
        // set first element to 1
        let mut d = nums;
        d.set(0, 1);
        d
    } else if mutation_kind == 5 {
        // set all elements to 0
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 100_000,
                forall|j: int| 0 <= j < i ==> d[j] == 0,
                forall|j: int| i <= j < d.len() ==> (#[trigger] d[j] == 0 || d[j] == 1),
            decreases d.len() - i,
        {
            d.set(i, 0);
            i += 1;
        }
        d
    } else if mutation_kind == 6 {
        // set all elements to 1
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 100_000,
                forall|j: int| 0 <= j < i ==> d[j] == 1,
                forall|j: int| i <= j < d.len() ==> (#[trigger] d[j] == 0 || d[j] == 1),
            decreases d.len() - i,
        {
            d.set(i, 1);
            i += 1;
        }
        d
    } else if mutation_kind == 7 && nums.len() < 100_000 {
        // grow by one element (append 0)
        let mut d = nums;
        d.push(0);
        d
    } else if mutation_kind == 8 && nums.len() < 100_000 {
        // grow by one element (append 1)
        let mut d = nums;
        d.push(1);
        d
    } else if mutation_kind == 9 && nums.len() > 1 {
        // shrink by one element
        let mut d = nums;
        d.pop();
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
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
    fn gen_u8(&mut self) -> u8 {
        (self.next_u64() % 256) as u8
    }
}

struct Solution;
include!("../code.rs");

fn random_binary_array(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_usize(0, 1) as i32);
    }
    v
}

extern crate serde_json;
use serde_json::json;

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
        if *count >= target { return; }
        let key = format!("{:?}", nums);
        if !seen.insert(key) { return; }
        let output = Solution::prefixes_div_by5(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description
    let examples: Vec<Vec<i32>> = vec![
        vec![0, 1, 1],
        vec![1, 1, 1],
    ];

    // Interesting seed arrays
    let seeds: Vec<Vec<i32>> = vec![
        vec![0],
        vec![1],
        vec![1, 0],
        vec![0, 1],
        vec![1, 0, 1],
        vec![1, 0, 1, 0, 0],  // = 20, divisible by 5
        vec![0, 0, 0, 0, 0],
        vec![1, 1, 1, 1, 1],
        vec![1, 1, 0, 0, 1],
        vec![1, 1, 1, 1, 0],  // = 30, divisible by 5
    ];

    let mutation_kinds: Vec<u8> = (0..=9).collect();

    // Emit examples with identity mutation
    for ex in &examples {
        emit(generate_test_case(ex.clone(), 0), &mut seen, &mut out, &mut count);
    }

    // Apply every mutation to every seed
    for s in &seeds {
        for &mk in &mutation_kinds {
            emit(generate_test_case(s.clone(), mk), &mut seen, &mut out, &mut count);
        }
    }

    // Size classes with random mutations
    let size_classes: Vec<(usize, usize)> = vec![
        (1, 5),
        (6, 20),
        (21, 100),
        (101, 1000),
        (1001, 10000),
    ];

    for &(lo, hi) in &size_classes {
        for _ in 0..8 {
            if count >= target { break; }
            let len = rng.gen_range_usize(lo, hi);
            let arr = random_binary_array(&mut rng, len);
            let mk = rng.gen_u8() % 10;
            let result = generate_test_case(arr, mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Fill remaining with random arrays and random mutations
    while count < target {
        let len = rng.gen_range_usize(1, 100_000);
        let arr = random_binary_array(&mut rng, len);
        let mk = rng.gen_u8() % 10;
        let result = generate_test_case(arr, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }
}
