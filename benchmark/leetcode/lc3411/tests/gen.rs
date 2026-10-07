use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        2 <= nums.len() <= 100,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 10,
    ensures
        2 <= result.len() <= 100,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 10,
{
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 {
        // set last element to 1 (boundary low)
        let mut r = nums;
        let last = r.len() - 1;
        r.set(last, 1);
        r
    } else if mutation_kind == 2 {
        // set last element to 10 (boundary high)
        let mut r = nums;
        let last = r.len() - 1;
        r.set(last, 10);
        r
    } else if mutation_kind == 3 {
        // set all elements to 1
        let mut r = nums;
        let mut i: usize = 0;
        while i < r.len()
            invariant
                0 <= i <= r.len(),
                r.len() == nums.len(),
                2 <= r.len() <= 100,
                forall|j: int| 0 <= j < i ==> r[j] == 1i32,
                forall|j: int| i <= j < r.len() ==> r[j] == nums[j],
            decreases r.len() - i,
        {
            r.set(i, 1);
            i += 1;
        }
        r
    } else if mutation_kind == 4 && nums.len() < 100 {
        // grow by one element (push 1)
        let mut r = nums;
        r.push(1);
        r
    } else if mutation_kind == 5 && nums.len() > 2 {
        // shrink by one element (pop)
        let mut r = nums;
        r.pop();
        r
    } else if mutation_kind == 6 {
        // nudge last element up (if < 10, increment)
        let mut r = nums;
        let last = r.len() - 1;
        if r[last] < 10 {
            r.set(last, r[last] + 1);
        }
        r
    } else if mutation_kind == 7 {
        // nudge last element down (if > 1, decrement)
        let mut r = nums;
        let last = r.len() - 1;
        if r[last] > 1 {
            r.set(last, r[last] - 1);
        }
        r
    } else if mutation_kind == 8 && nums.len() >= 2 {
        // swap first and last elements
        let mut r = nums;
        let last = r.len() - 1;
        let first_val = r[0];
        let last_val = r[last];
        r.set(0, last_val);
        if last > 0 {
            r.set(last, first_val);
        }
        assert forall|j: int| 0 <= j < r.len() implies 1 <= #[trigger] r[j] <= 10 by {
            if j == 0 {
                assert(r[0] == last_val);
            } else if j == last as int {
                assert(r[last as int] == first_val);
            } else {
                assert(r[j] == nums[j]);
            }
        }
        r
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

extern crate serde_json;
use serde_json::json;

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(1, 10) as i32);
    }
    nums
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(3411);
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
        let output = Solution::max_length(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let example_seeds: Vec<Vec<i32>> = vec![
        vec![1, 2, 1, 2, 1, 1, 1],
        vec![2, 3, 4, 5, 6],
        vec![1, 2, 3, 1, 4, 5, 1],
    ];

    // Additional interesting seeds
    let extra_seeds: Vec<Vec<i32>> = vec![
        vec![1, 1],
        vec![10, 10],
        vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
        vec![2, 4, 8],
        vec![3, 6, 9],
        vec![5, 10],
        vec![7, 7],
        vec![1, 1, 1, 1, 1],
        vec![2, 3, 5, 7],
        vec![6, 6, 6],
        vec![4, 4],
        vec![8, 8],
        vec![1, 10],
        vec![10, 1],
        vec![1, 2],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8];

    // Apply every mutation to every example seed
    for seed in &example_seeds {
        for &mk in &mutation_kinds {
            let result = mutate(seed.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Apply mutations to extra seeds
    for seed in &extra_seeds {
        for &mk in &mutation_kinds {
            let result = mutate(seed.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds with random mutations across size classes
    while count < target {
        let len = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(2, 5),    // tiny
            1 => rng.gen_range_usize(2, 10),   // small
            2 => rng.gen_range_usize(11, 30),  // medium
            3 => rng.gen_range_usize(31, 60),  // large
            _ => rng.gen_range_usize(61, 100), // max
        };
        let seed = random_nums(&mut rng, len);
        let mk = rng.gen_range_usize(0, 8) as u8;
        let result = mutate(seed, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }
}
