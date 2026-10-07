use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, k: i32, mutation_kind: u8) -> (res: (Vec<i32>, i32))
    requires
        1 <= nums.len() <= 1000,
        0 <= k <= 10,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums@[i],
        forall|i: int| 0 <= i < nums.len() ==> #[trigger] nums@[i] <= 100000,
    ensures
        1 <= res.0.len() <= 1000,
        0 <= res.1 <= 10,
        forall|i: int| 0 <= i < res.0.len() ==> 1 <= #[trigger] res.0@[i],
        forall|i: int| 0 <= i < res.0.len() ==> #[trigger] res.0@[i] <= 100000,
{
    if mutation_kind == 0 {
        // identity
        (nums, k)
    } else if mutation_kind == 1 {
        // nudge last element up
        let mut d = nums;
        let last = d.len() - 1;
        if d[last] < 100000 {
            d.set(last, d[last] + 1);
        }
        (d, k)
    } else if mutation_kind == 2 {
        // nudge last element down
        let mut d = nums;
        let last = d.len() - 1;
        if d[last] > 1 {
            d.set(last, d[last] - 1);
        }
        (d, k)
    } else if mutation_kind == 3 {
        // set last element to 1 (min value)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 1);
        (d, k)
    } else if mutation_kind == 4 {
        // set last element to 100000 (max value)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 100000);
        (d, k)
    } else if mutation_kind == 5 && nums.len() < 1000 {
        // grow array by one element
        let mut d = nums;
        d.push(1);
        (d, k)
    } else if mutation_kind == 6 && nums.len() > 1 {
        // shrink array by one element
        let mut d = nums;
        d.pop();
        (d, k)
    } else if mutation_kind == 7 {
        // set all elements to 1
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 1000,
                forall|j: int| 0 <= j < i ==> d[j] == 1i32,
                forall|j: int| i <= j < d.len() ==> d[j] == nums@[j],
            decreases d.len() - i,
        {
            d.set(i, 1);
            i += 1;
        }
        (d, k)
    } else if mutation_kind == 8 && k < 10 {
        // k + 1
        (nums, k + 1)
    } else if mutation_kind == 9 && k > 0 {
        // k - 1
        (nums, k - 1)
    } else if mutation_kind == 10 {
        // set k to 0
        (nums, 0)
    } else if mutation_kind == 11 {
        // set k to 10
        (nums, 10)
    } else if mutation_kind == 12 {
        // set first element to 100000
        let mut d = nums;
        d.set(0, 100000);
        (d, k)
    } else {
        // fallback: identity
        (nums, k)
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

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(1, 100000) as i32);
    }
    nums
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2859);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;
    let num_mutations: u8 = 13;

    let mut emit = |nums: Vec<i32>, k: i32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count {
            return;
        }
        let key = format!("{:?}:{}", nums, k);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::sum_indices_with_k_set_bits(nums.clone(), k);
        writeln!(out, "{}", json!({"input": {"nums": nums, "k": k}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<(Vec<i32>, i32)> = vec![
        (vec![5, 10, 1, 5, 2], 1),
        (vec![4, 3, 2, 1], 2),
    ];

    for (nums, k) in &examples {
        for mk in 0..num_mutations {
            let (res_nums, res_k) = generate_test_case(nums.clone(), *k, mk);
            emit(res_nums, res_k, &mut seen, &mut out, &mut count);
        }
    }

    // Seed pool: diverse array sizes and value distributions
    let size_classes: Vec<usize> = vec![1, 2, 3, 5, 10, 50, 100, 500, 1000];
    let k_values: Vec<i32> = vec![0, 1, 2, 3, 5, 7, 10];

    // Generate seeds across size classes and k values
    for &n in &size_classes {
        for &k in &k_values {
            if count >= target_count { break; }
            let nums = random_nums(&mut rng, n);
            for mk in 0..num_mutations {
                let (res_nums, res_k) = generate_test_case(nums.clone(), k, mk);
                emit(res_nums, res_k, &mut seen, &mut out, &mut count);
            }
        }
    }

    // Boundary value arrays
    let boundary_seeds: Vec<Vec<i32>> = vec![
        vec![1],                         // single min element
        vec![100000],                    // single max element
        vec![1, 1, 1, 1, 1],            // all minimum
        vec![100000, 100000, 100000],    // all maximum
        vec![50000],                     // midpoint
    ];

    for nums in &boundary_seeds {
        for &k in &k_values {
            for mk in 0..num_mutations {
                let (res_nums, res_k) = generate_test_case(nums.clone(), k, mk);
                emit(res_nums, res_k, &mut seen, &mut out, &mut count);
            }
        }
    }

    // Fill remaining with random seeds + random mutations
    while count < target_count {
        let n = match count % 5 {
            0 => rng.gen_range_usize(1, 5),       // tiny
            1 => rng.gen_range_usize(1, 10),      // small
            2 => rng.gen_range_usize(11, 100),    // medium
            3 => rng.gen_range_usize(101, 500),   // large
            _ => rng.gen_range_usize(501, 1000),  // max
        };
        let nums = random_nums(&mut rng, n);
        let k = rng.gen_range_i64(0, 10) as i32;
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let (res_nums, res_k) = generate_test_case(nums, k, mk);
        emit(res_nums, res_k, &mut seen, &mut out, &mut count);
    }
}
