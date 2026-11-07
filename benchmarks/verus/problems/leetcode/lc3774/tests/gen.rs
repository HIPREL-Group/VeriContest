use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, k: i32, mutation_kind: u8) -> (result: (Vec<i32>, i32))
    requires
        1 <= nums.len() <= 100,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
        1 <= k <= nums.len(),
    ensures
        1 <= result.0.len() <= 100,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 100,
        1 <= result.1 <= result.0.len(),
{
    if mutation_kind == 0 {
        // identity
        (nums, k)
    } else if mutation_kind == 1 {
        // set first element to 1 (min boundary)
        let mut d = nums;
        d.set(0, 1);
        (d, k)
    } else if mutation_kind == 2 {
        // set first element to 100 (max boundary)
        let mut d = nums;
        d.set(0, 100);
        (d, k)
    } else if mutation_kind == 3 {
        // set all elements to 1
        let mut d = nums;
        let n = d.len();
        let mut i: usize = 0;
        while i < n
            invariant
                n == d.len(),
                1 <= n <= 100,
                0 <= i <= n,
                forall|j: int| 0 <= j < i ==> d[j] == 1i32,
            decreases n - i,
        {
            d.set(i, 1);
            i += 1;
        }
        (d, k)
    } else if mutation_kind == 4 {
        // set all elements to 100
        let mut d = nums;
        let n = d.len();
        let mut i: usize = 0;
        while i < n
            invariant
                n == d.len(),
                1 <= n <= 100,
                0 <= i <= n,
                forall|j: int| 0 <= j < i ==> d[j] == 100i32,
            decreases n - i,
        {
            d.set(i, 100);
            i += 1;
        }
        (d, k)
    } else if mutation_kind == 5 && nums.len() < 100 {
        // grow array by one element (push 50)
        let mut d = nums;
        d.push(50);
        (d, k)
    } else if mutation_kind == 6 && nums.len() > 1 && k < nums.len() as i32 {
        // shrink array by one element (pop)
        let mut d = nums;
        d.pop();
        (d, k)
    } else if mutation_kind == 7 {
        // nudge first element up (if < 100)
        let mut d = nums;
        if d[0] < 100 {
            d.set(0, d[0] + 1);
        }
        (d, k)
    } else if mutation_kind == 8 {
        // nudge first element down (if > 1)
        let mut d = nums;
        if d[0] > 1 {
            d.set(0, d[0] - 1);
        }
        (d, k)
    } else if mutation_kind == 9 {
        // set k = 1 (min k)
        (nums, 1)
    } else if mutation_kind == 10 {
        // set k = nums.len() (max k)
        let new_k = nums.len() as i32;
        (nums, new_k)
    } else if mutation_kind == 11 {
        // set last element to 1
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 1);
        (d, k)
    } else if mutation_kind == 12 {
        // set last element to 100
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 100);
        (d, k)
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

fn mutate(nums: Vec<i32>, k: i32, mutation_kind: u8) -> (Vec<i32>, i32) {
    generate_test_case(nums, k, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(1, 100) as i32);
    }
    nums
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(3774);
    let count_target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>, k: i32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= count_target {
            return;
        }
        let key = format!("{:?}_{}", nums, k);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::abs_difference(nums.clone(), k);
        writeln!(out, "{}", json!({"input": {"nums": nums, "k": k}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from the problem description
    emit(vec![5, 2, 2, 4], 2, &mut seen, &mut out, &mut count);
    emit(vec![100], 1, &mut seen, &mut out, &mut count);

    // Seed inputs with known interesting properties
    let seeds: Vec<(Vec<i32>, i32)> = vec![
        (vec![1], 1),
        (vec![1, 100], 1),
        (vec![1, 100], 2),
        (vec![50, 50, 50], 2),
        (vec![1, 1, 1, 1], 2),
        (vec![100, 100, 100], 3),
        (vec![1, 2, 3, 4, 5], 3),
        (vec![1, 2, 3, 4, 5], 1),
        (vec![1, 2, 3, 4, 5], 5),
        (vec![99, 100, 1, 2], 2),
    ];

    let mutation_kinds: Vec<u8> = (0..=12).collect();

    // Apply every mutation to every seed
    for (s_nums, s_k) in &seeds {
        for &mk in &mutation_kinds {
            let (result_nums, result_k) = mutate(s_nums.clone(), *s_k, mk);
            emit(result_nums, result_k, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds with random mutations across size classes
    while count < count_target {
        let n: usize = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 3),        // tiny
            1 => rng.gen_range_usize(1, 10),        // small
            2 => rng.gen_range_usize(11, 50),       // medium
            3 => rng.gen_range_usize(51, 100),      // large
            _ => rng.gen_range_usize(1, 100),       // fallback
        };
        let nums = random_nums(&mut rng, n);
        let k = rng.gen_range_i64(1, n as i64) as i32;
        let mk = rng.gen_range_usize(0, 12) as u8;
        let (result_nums, result_k) = mutate(nums, k, mk);
        emit(result_nums, result_k, &mut seen, &mut out, &mut count);
    }
}
