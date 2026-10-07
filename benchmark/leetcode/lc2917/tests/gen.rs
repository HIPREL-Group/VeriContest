use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    nums: Vec<i32>,
    k: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= nums.len() <= 50,
        1 <= k <= nums.len(),
        forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] < 2_147_483_648,
    ensures
        1 <= result.0.len() <= 50,
        1 <= result.1 <= result.0.len(),
        forall|i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] < 2_147_483_648,
{
    if mutation_kind == 0 {
        // identity
        (nums, k)
    } else if mutation_kind == 1 {
        // set last element to 0
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 0);
        (d, k)
    } else if mutation_kind == 2 {
        // set last element to max (2^31 - 1 = 2_147_483_647)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 2_147_483_647);
        (d, k)
    } else if mutation_kind == 3 {
        // set all elements to 0
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 50,
                forall|j: int| 0 <= j < i ==> d[j] == 0i32,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 0);
            i += 1;
        }
        (d, k)
    } else if mutation_kind == 4 {
        // set k to 1
        (nums, 1)
    } else if mutation_kind == 5 {
        // set k to nums.len()
        let n = nums.len() as i32;
        (nums, n)
    } else if mutation_kind == 6 {
        // nudge first element up (if < max)
        let mut d = nums;
        if d[0] < 2_147_483_646 {
            d.set(0, d[0] + 1);
        }
        (d, k)
    } else if mutation_kind == 7 {
        // nudge first element down (if > 0)
        let mut d = nums;
        if d[0] > 0 {
            d.set(0, d[0] - 1);
        }
        (d, k)
    } else if mutation_kind == 8 && nums.len() < 50 {
        // grow: push a 0
        let mut d = nums;
        d.push(0);
        // k is still valid since len grew
        (d, k)
    } else if mutation_kind == 9 && nums.len() > 1 && k < nums.len() as i32 {
        // shrink: pop last element (only if k < len so k stays valid)
        let mut d = nums;
        d.pop();
        (d, k)
    } else if mutation_kind == 10 {
        // set all elements to max value
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 50,
                forall|j: int| 0 <= j < i ==> d[j] == 2_147_483_647i32,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 2_147_483_647);
            i += 1;
        }
        (d, k)
    } else if mutation_kind == 11 && nums.len() >= 2 {
        // swap first two elements
        let mut d = nums;
        let tmp = d[0];
        d.set(0, d[1]);
        d.set(1, tmp);
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
        self.0 = self.0
            .wrapping_mul(6364136223846793005)
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

fn gen(nums: Vec<i32>, k: i32, mutation_kind: u8) -> (Vec<i32>, i32) {
    generate_test_case(nums, k, mutation_kind)
}

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(0, 2_147_483_647) as i32);
    }
    nums
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::collections::HashSet;
    use std::io::Write;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2917);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!())
        .parent()
        .unwrap()
        .join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>,
                    k: i32,
                    seen: &mut HashSet<String>,
                    out: &mut std::io::BufWriter<std::fs::File>,
                    count: &mut usize| {
        if *count >= target {
            return;
        }
        let key = format!("{:?}_{}", nums, k);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::find_k_or(nums.clone(), k);
        writeln!(
            out,
            "{}",
            json!({"input": {"nums": nums, "k": k}, "output": output})
        )
        .unwrap();
        *count += 1;
    };

    // Example inputs from problem description
    let examples: Vec<(Vec<i32>, i32)> = vec![
        (vec![7, 12, 9, 8, 9, 15], 4),
        (vec![2, 12, 1, 11, 4, 5], 6),
        (vec![10, 8, 5, 9, 11, 6, 8], 1),
    ];
    for (nums, k) in &examples {
        emit(nums.clone(), *k, &mut seen, &mut out, &mut count);
    }

    // Seed arrays × mutation kinds
    let seed_arrays: Vec<(Vec<i32>, i32)> = vec![
        (vec![0], 1),
        (vec![2_147_483_647], 1),
        (vec![1, 2, 3, 4, 5], 3),
        (vec![0, 0, 0, 0], 2),
        (vec![2_147_483_647; 10], 5),
        (vec![1], 1),
        (vec![255, 128, 64, 32, 16, 8, 4, 2, 1], 4),
        (vec![1023, 512, 256], 2),
    ];
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];

    for (nums, k) in &seed_arrays {
        for &mk in &mutation_kinds {
            let (rn, rk) = gen(nums.clone(), *k, mk);
            emit(rn, rk, &mut seen, &mut out, &mut count);
        }
    }

    // Random inputs with random mutations
    while count < target {
        let n = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 3),   // tiny
            1 => rng.gen_range_usize(1, 10),   // small
            2 => rng.gen_range_usize(11, 30),  // medium
            3 => rng.gen_range_usize(31, 50),  // large
            _ => rng.gen_range_usize(1, 50),   // any
        };
        let nums = random_nums(&mut rng, n);
        let k = rng.gen_range_usize(1, n) as i32;
        let mk = rng.gen_range_usize(0, 11) as u8;
        let (rn, rk) = gen(nums, k, mk);
        emit(rn, rk, &mut seen, &mut out, &mut count);
    }
}
