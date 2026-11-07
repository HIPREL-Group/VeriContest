use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= nums.len() <= 1000,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100_000,
    ensures
        1 <= result.len() <= 1000,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 100_000,
{
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 {
        // set last element to 1 (min boundary)
        let mut v = nums;
        let last = v.len() - 1;
        v.set(last, 1);
        v
    } else if mutation_kind == 2 {
        // set last element to 100_000 (max boundary)
        let mut v = nums;
        let last = v.len() - 1;
        v.set(last, 100_000);
        v
    } else if mutation_kind == 3 {
        // set all elements to 1
        let mut v = nums;
        let mut i: usize = 0;
        while i < v.len()
            invariant
                0 <= i <= v.len(),
                v.len() == nums.len(),
                1 <= v.len() <= 1000,
                forall|j: int| 0 <= j < i ==> v[j] == 1i32,
                forall|j: int| i <= j < v.len() ==> v[j] == nums[j],
            decreases v.len() - i,
        {
            v.set(i, 1);
            i += 1;
        }
        v
    } else if mutation_kind == 4 {
        // set all elements to 100_000
        let mut v = nums;
        let mut i: usize = 0;
        while i < v.len()
            invariant
                0 <= i <= v.len(),
                v.len() == nums.len(),
                1 <= v.len() <= 1000,
                forall|j: int| 0 <= j < i ==> v[j] == 100_000i32,
                forall|j: int| i <= j < v.len() ==> v[j] == nums[j],
            decreases v.len() - i,
        {
            v.set(i, 100_000);
            i += 1;
        }
        v
    } else if mutation_kind == 5 && nums.len() < 1000 {
        // grow by one element
        let mut v = nums;
        v.push(1);
        v
    } else if mutation_kind == 6 && nums.len() > 1 {
        // shrink by one element
        let mut v = nums;
        v.pop();
        v
    } else if mutation_kind == 7 {
        // nudge first element up (if < 100_000)
        let mut v = nums;
        if v[0] < 100_000 {
            v.set(0, v[0] + 1);
        }
        v
    } else if mutation_kind == 8 {
        // nudge last element down (if > 1)
        let mut v = nums;
        let last = v.len() - 1;
        if v[last] > 1 {
            v.set(last, v[last] - 1);
        }
        v
    } else if mutation_kind == 9 && nums.len() >= 2 {
        // swap first and last elements
        let mut v = nums;
        let last = v.len() - 1;
        let first_val = v[0];
        let last_val = v[last];
        v.set(0, last_val);
        if last != 0 {
            v.set(last, first_val);
        }
        v
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

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(1, 100_000) as i32);
    }
    nums
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut emitted = 0usize;

    let mut emit = |nums: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, emitted: &mut usize| {
        if *emitted >= count {
            return;
        }
        let key = format!("{:?}", nums);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::left_right_difference(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *emitted += 1;
    };

    // Example test cases from description
    emit(vec![10, 4, 8, 3], &mut seen, &mut out, &mut emitted);
    emit(vec![1], &mut seen, &mut out, &mut emitted);

    // Seed pool: boundary and interesting arrays
    let seeds: Vec<Vec<i32>> = vec![
        vec![1],
        vec![100_000],
        vec![1, 1],
        vec![100_000, 100_000],
        vec![1, 100_000],
        vec![100_000, 1],
        vec![50_000, 50_000, 50_000],
        vec![1, 2, 3, 4, 5],
        vec![5, 4, 3, 2, 1],
        vec![1; 1000],
    ];

    // Apply all mutations to each seed
    for s in &seeds {
        for mk in 0..10u8 {
            if emitted >= count { break; }
            let result = generate_test_case(s.clone(), mk);
            emit(result, &mut seen, &mut out, &mut emitted);
        }
    }

    // Random test cases with size classes and mutations
    while emitted < count {
        let n: usize = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 5),       // tiny
            1 => rng.gen_range_usize(1, 10),       // small
            2 => rng.gen_range_usize(11, 100),     // medium
            3 => rng.gen_range_usize(101, 500),    // large
            _ => rng.gen_range_usize(501, 1000),   // max
        };
        let nums = random_nums(&mut rng, n);
        let mk = rng.gen_range_usize(0, 9) as u8;
        let result = generate_test_case(nums, mk);
        emit(result, &mut seen, &mut out, &mut emitted);
    }
}
