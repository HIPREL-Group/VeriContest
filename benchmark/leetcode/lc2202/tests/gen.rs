use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, k: i32, mutation_kind: u8) -> (result: (Vec<i32>, i32))
    requires
        1 <= nums.len() <= 100_000,
        0 <= k <= 1_000_000_000,
        forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1_000_000_000,
    ensures
        1 <= result.0.len() <= 100_000,
        0 <= result.1 <= 1_000_000_000,
        forall|i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 1_000_000_000,
{
    if mutation_kind == 0 {
        (nums, k)
    } else if mutation_kind == 1 && k < 1_000_000_000 {
        (nums, k + 1)
    } else if mutation_kind == 2 && k > 0 {
        (nums, k - 1)
    } else if mutation_kind == 3 {
        (nums, 0)
    } else if mutation_kind == 4 {
        (nums, 1)
    } else if mutation_kind == 5 {
        let mut v = nums;
        v.set(0, 0);
        (v, k)
    } else if mutation_kind == 6 {
        let mut v = nums;
        v.set(0, 1_000_000_000);
        (v, k)
    } else if mutation_kind == 7 && nums.len() < 100_000 {
        let mut v = nums;
        v.push(0);
        (v, k)
    } else if mutation_kind == 8 && nums.len() > 1 {
        let mut v = nums;
        v.pop();
        (v, k)
    } else if mutation_kind == 9 && nums.len() >= 2 {
        let mut v = nums;
        let a = v[0];
        let b = v[1];
        v.set(0, b);
        v.set(1, a);
        (v, k)
    } else if mutation_kind == 10 {
        let val = nums[0];
        let ghost n = nums.len();
        let mut v = nums;
        let mut i: usize = 0;
        while i < v.len()
            invariant
                0 <= i <= v.len(),
                v.len() == n,
                1 <= v.len() <= 100_000,
                0 <= val <= 1_000_000_000,
                forall|j: int| 0 <= j < i ==> v[j] == val,
            decreases v.len() - i,
        {
            v.set(i, val);
            i += 1;
        }
        (v, k)
    } else if mutation_kind == 11 {
        let nlen = nums.len() as i32;
        if nlen >= 0 && nlen <= 1_000_000_000 {
            (nums, nlen)
        } else {
            (nums, k)
        }
    } else if mutation_kind == 12 {
        (nums, 1_000_000_000)
    } else {
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

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(0, 1_000_000_000) as i32);
    }
    v
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2202);
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
        let output = Solution::maximum_top(nums.clone(), k);
        writeln!(out, "{}", json!({"input": {"nums": nums, "k": k}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    emit(vec![5, 2, 2, 4, 0, 6], 4, &mut seen, &mut out, &mut count);
    emit(vec![2], 1, &mut seen, &mut out, &mut count);

    // Interesting seed cases
    let seed_cases: Vec<(Vec<i32>, i32)> = vec![
        (vec![1], 0),
        (vec![1], 2),
        (vec![1], 3),
        (vec![1, 2], 0),
        (vec![1, 2], 1),
        (vec![1, 2], 2),
        (vec![1, 2], 3),
        (vec![3, 1], 1),
        (vec![1, 3], 1),
        (vec![0, 0, 0], 5),
        (vec![1_000_000_000], 0),
        (vec![1_000_000_000], 1),
        (vec![0], 0),
        (vec![0], 1_000_000_000),
        (vec![5, 4, 3, 2, 1], 3),
        (vec![1, 2, 3, 4, 5], 3),
    ];
    for (nums, k) in &seed_cases {
        emit(nums.clone(), *k, &mut seen, &mut out, &mut count);
    }

    let mutation_kinds: Vec<u8> = (0..=12).collect();

    for (nums, k) in &seed_cases {
        for &mk in &mutation_kinds {
            if count >= target { break; }
            let (rn, rk) = mutate(nums.clone(), *k, mk);
            emit(rn, rk, &mut seen, &mut out, &mut count);
        }
    }

    // Random inputs with varied sizes
    for _ in 0..60 {
        if count >= target { break; }
        let n = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 1000),
            _ => rng.gen_range_usize(1001, 10000),
        };
        let nums = random_nums(&mut rng, n);
        let k = match rng.gen_range_usize(0, 5) {
            0 => rng.gen_range_i64(0, 5) as i32,
            1 => rng.gen_range_i64(0, n as i64) as i32,
            2 => rng.gen_range_i64(n as i64, (2 * n) as i64) as i32,
            3 => rng.gen_range_i64(0, 1_000_000_000) as i32,
            _ => 1_000_000_000,
        };
        let mk = rng.gen_range_usize(0, 12) as u8;
        let (rn, rk) = mutate(nums, k, mk);
        emit(rn, rk, &mut seen, &mut out, &mut count);
    }

    // Fill remaining with random
    while count < target {
        let n = rng.gen_range_usize(1, 1000);
        let nums = random_nums(&mut rng, n);
        let k = rng.gen_range_i64(0, 1_000_000_000) as i32;
        emit(nums, k, &mut seen, &mut out, &mut count);
    }
}
