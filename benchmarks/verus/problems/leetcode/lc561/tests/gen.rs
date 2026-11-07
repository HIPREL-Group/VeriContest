use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        2 <= nums.len() <= 20000,
        nums.len() % 2 == 0,
        forall|i: int| 0 <= i < nums.len() ==> -10000 <= #[trigger] nums[i] <= 10000,
    ensures
        2 <= result.len() <= 20000,
        result.len() % 2 == 0,
        forall|i: int| 0 <= i < result.len() ==> -10000 <= #[trigger] result[i] <= 10000,
{
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 {
        // set first element to max boundary
        let mut d = nums;
        d.set(0, 10000);
        d
    } else if mutation_kind == 2 {
        // set first element to min boundary
        let mut d = nums;
        d.set(0, -10000);
        d
    } else if mutation_kind == 3 {
        // set all elements to 0
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                2 <= d.len() <= 20000,
                d.len() % 2 == 0,
                forall|j: int| 0 <= j < i ==> d[j] == 0i32,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
                forall|j: int| 0 <= j < i ==> -10000 <= #[trigger] d[j] <= 10000,
                forall|j: int| i <= j < d.len() ==> -10000 <= #[trigger] d[j] <= 10000,
            decreases d.len() - i,
        {
            d.set(i, 0);
            i += 1;
        }
        d
    } else if mutation_kind == 4 && nums.len() <= 19998 {
        // grow by 2 elements (preserves even length)
        let mut d = nums;
        d.push(0);
        d.push(0);
        d
    } else if mutation_kind == 5 && nums.len() >= 4 {
        // shrink by 2 elements (preserves even length)
        let mut d = nums;
        d.pop();
        d.pop();
        d
    } else if mutation_kind == 6 {
        // nudge first element up
        let mut d = nums;
        if d[0] < 10000 {
            d.set(0, d[0] + 1);
        }
        d
    } else if mutation_kind == 7 {
        // nudge first element down
        let mut d = nums;
        if d[0] > -10000 {
            d.set(0, d[0] - 1);
        }
        d
    } else if mutation_kind == 8 && nums.len() >= 2 {
        // swap first two elements
        let mut d = nums;
        let a = d[0];
        let b = d[1];
        d.set(0, b);
        d.set(1, a);
        d
    } else if mutation_kind == 9 {
        // set last element to max boundary
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 10000);
        d
    } else if mutation_kind == 10 {
        // set last element to min boundary
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, -10000);
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

fn random_even_vec(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(-10000, 10000) as i32);
    }
    v
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(561);
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
        let output = Solution::array_pair_sum(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![1, 4, 3, 2],
        vec![6, 2, 6, 5, 1, 2],
    ];
    for ex in &examples {
        emit(ex.clone(), &mut seen, &mut out, &mut count);
    }

    // Hand-crafted seeds
    let seeds: Vec<Vec<i32>> = vec![
        vec![-10000, 10000],                        // min pair, boundary values
        vec![0, 0],                                 // zeros
        vec![1, 1, 1, 1],                           // all same
        vec![-1, -1, -1, -1],                       // all same negative
        vec![10000, 10000, -10000, -10000],          // extreme boundaries
        vec![0, 1, 2, 3, 4, 5],                     // sorted ascending
        vec![5, 4, 3, 2, 1, 0],                     // sorted descending
        vec![1, -1, 2, -2, 3, -3, 4, -4],           // alternating sign
        vec![9999, 10000, -9999, -10000],            // near-boundary
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

    // Apply every mutation to every seed
    for s in &seeds {
        for &mk in &mutation_kinds {
            emit(mutate(s.clone(), mk), &mut seen, &mut out, &mut count);
        }
    }

    // Size classes with random mutations
    let size_classes: Vec<(usize, usize)> = vec![
        (2, 4),         // tiny
        (4, 10),        // small
        (10, 100),      // medium
        (100, 1000),    // large
        (1000, 20000),  // max
    ];

    for &(lo, hi) in &size_classes {
        for _ in 0..5 {
            let mut len = rng.gen_range_usize(lo / 2, hi / 2) * 2; // ensure even
            if len < 2 { len = 2; }
            if len > 20000 { len = 20000; }
            let v = random_even_vec(&mut rng, len);
            let mk = rng.gen_range_usize(0, 10) as u8;
            emit(mutate(v, mk), &mut seen, &mut out, &mut count);
        }
    }

    // Fill remaining with random vectors and identity mutation
    while count < target {
        let mut len = rng.gen_range_usize(1, 10000) * 2; // ensure even
        if len < 2 { len = 2; }
        if len > 20000 { len = 20000; }
        let v = random_even_vec(&mut rng, len);
        let mk = rng.gen_range_usize(0, 10) as u8;
        emit(mutate(v, mk), &mut seen, &mut out, &mut count);
    }
}
