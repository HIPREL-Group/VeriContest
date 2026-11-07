use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, k: i32, mutation_kind: u8) -> (result: (Vec<i32>, i32))
    requires
        1 <= nums.len() <= 200000,
        forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1_000_000_000,
        0 <= k <= 1_000_000_000,
    ensures
        1 <= result.0.len() <= 200000,
        forall|i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 1_000_000_000,
        0 <= result.1 <= 1_000_000_000,
{
    if mutation_kind == 0 {
        // identity
        (nums, k)
    } else if mutation_kind == 1 {
        // set last element to 0
        let mut v = nums;
        let last = v.len() - 1;
        v.set(last, 0);
        (v, k)
    } else if mutation_kind == 2 {
        // set last element to 1_000_000_000 (max boundary)
        let mut v = nums;
        let last = v.len() - 1;
        v.set(last, 1_000_000_000);
        (v, k)
    } else if mutation_kind == 3 {
        // set first element to 0
        let mut v = nums;
        v.set(0, 0);
        (v, k)
    } else if mutation_kind == 4 && nums.len() < 200000 {
        // grow array by one element (push 0)
        let mut v = nums;
        v.push(0);
        (v, k)
    } else if mutation_kind == 5 && nums.len() > 1 {
        // shrink array by one element (pop)
        let mut v = nums;
        v.pop();
        (v, k)
    } else if mutation_kind == 6 {
        // set k to 0
        (nums, 0)
    } else if mutation_kind == 7 {
        // set k to max boundary
        (nums, 1_000_000_000)
    } else if mutation_kind == 8 {
        // set all elements to 0
        let mut v = nums;
        let mut i: usize = 0;
        while i < v.len()
            invariant
                0 <= i <= v.len(),
                v.len() == nums.len(),
                1 <= v.len() <= 200000,
                forall|j: int| 0 <= j < i ==> v[j] == 0i32,
                forall|j: int| i <= j < v.len() ==> v[j] == nums[j],
            decreases v.len() - i,
        {
            v.set(i, 0);
            i += 1;
        }
        (v, k)
    } else if mutation_kind == 9 {
        // set all elements to 1_000_000_000
        let mut v = nums;
        let mut i: usize = 0;
        while i < v.len()
            invariant
                0 <= i <= v.len(),
                v.len() == nums.len(),
                1 <= v.len() <= 200000,
                forall|j: int| 0 <= j < i ==> v[j] == 1_000_000_000i32,
                forall|j: int| i <= j < v.len() ==> v[j] == nums[j],
            decreases v.len() - i,
        {
            v.set(i, 1_000_000_000);
            i += 1;
        }
        (v, k)
    } else if mutation_kind == 10 && nums.len() >= 2 {
        // swap first and last elements
        let mut v = nums;
        let last = v.len() - 1;
        let tmp = v[0];
        v.set(0, v[last]);
        v.set(last, tmp);
        (v, k)
    } else if mutation_kind == 11 {
        // nudge last element up (if below max)
        let mut v = nums;
        let last = v.len() - 1;
        if v[last] < 1_000_000_000 {
            v.set(last, v[last] + 1);
        }
        (v, k)
    } else if mutation_kind == 12 {
        // nudge last element down (if above 0)
        let mut v = nums;
        let last = v.len() - 1;
        if v[last] > 0 {
            v.set(last, v[last] - 1);
        }
        (v, k)
    } else if mutation_kind == 13 && k < 1_000_000_000 {
        // nudge k up
        (nums, k + 1)
    } else if mutation_kind == 14 && k > 0 {
        // nudge k down
        (nums, k - 1)
    } else {
        // fallback: identity
        (nums, k)
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

fn mutate(nums: Vec<i32>, k: i32, mutation_kind: u8) -> (Vec<i32>, i32) {
    generate_test_case(nums, k, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(0, 1_000_000_000) as i32);
    }
    v
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(3097);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>, k: i32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target {
            return;
        }
        let key = format!("{:?}_{}", nums, k);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::minimum_subarray_length(nums.clone(), k);
        writeln!(out, "{}", json!({"input": {"nums": nums, "k": k}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<(Vec<i32>, i32)> = vec![
        (vec![1, 2, 3], 2),
        (vec![2, 1, 8], 10),
        (vec![1, 2], 0),
    ];
    for (nums, k) in examples {
        emit(nums, k, &mut seen, &mut out, &mut count);
    }

    // Curated seed inputs covering edge cases
    let seed_inputs: Vec<(Vec<i32>, i32)> = vec![
        (vec![0], 0),
        (vec![0], 1),
        (vec![1_000_000_000], 1_000_000_000),
        (vec![1_000_000_000], 0),
        (vec![0, 0, 0], 1),
        (vec![1, 1, 1, 1], 1),
        (vec![7, 3, 5], 7),
        (vec![1, 2, 4, 8], 15),
        (vec![1, 2, 4, 8], 16),
        (vec![0, 0, 0, 0, 0], 0),
    ];

    let mutation_kinds: Vec<u8> = (0..=14).collect();

    // Apply every mutation to seed inputs
    for (nums, k) in &seed_inputs {
        for &mk in &mutation_kinds {
            let (r_nums, r_k) = mutate(nums.clone(), *k, mk);
            emit(r_nums, r_k, &mut seen, &mut out, &mut count);
        }
    }

    // Random inputs with random mutations across size classes
    while count < target {
        let n: usize = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 5),       // tiny
            1 => rng.gen_range_usize(1, 10),       // small
            2 => rng.gen_range_usize(11, 100),     // medium
            3 => rng.gen_range_usize(101, 1000),   // large
            _ => rng.gen_range_usize(1001, 10000), // very large
        };
        let nums = random_nums(&mut rng, n);

        // Mix of k values: boundary and random
        let k: i32 = match rng.gen_range_usize(0, 4) {
            0 => 0,
            1 => 1,
            2 => 1_000_000_000,
            _ => rng.gen_range_i64(0, 1_000_000_000) as i32,
        };

        let mk = rng.gen_range_usize(0, 14) as u8;
        let (r_nums, r_k) = mutate(nums, k, mk);
        emit(r_nums, r_k, &mut seen, &mut out, &mut count);
    }
}
