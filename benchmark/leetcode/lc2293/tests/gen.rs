use vstd::prelude::*;

verus! {

pub open spec fn pow2(k: int) -> int
    decreases k,
{
    if k <= 0 { 1 } else { 2 * pow2(k - 1) }
}

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= nums.len() <= 1024,
        exists |k: int| 0 <= k <= 10 && nums.len() == pow2(k),
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000_000,
    ensures
        1 <= result.len() <= 1024,
        exists |k: int| 0 <= k <= 10 && result.len() == pow2(k),
        forall |i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 1_000_000_000,
{
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 {
        // set first element to 1 (min boundary)
        let mut d = nums;
        d.set(0, 1);
        d
    } else if mutation_kind == 2 {
        // set first element to max boundary
        let mut d = nums;
        d.set(0, 1_000_000_000);
        d
    } else if mutation_kind == 3 {
        // set last element to 1 (min boundary)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 1);
        d
    } else if mutation_kind == 4 {
        // set last element to max boundary
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 1_000_000_000);
        d
    } else if mutation_kind == 5 {
        // set all elements to 1
        let n = nums.len();
        let mut d = nums;
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                d.len() == n,
                1 <= n <= 1024,
                exists |k: int| 0 <= k <= 10 && n == pow2(k),
                forall |j: int| 0 <= j < i ==> d[j] == 1i32,
                forall |j: int| i <= j < n as int ==> d[j] == nums[j],
            decreases n - i,
        {
            d.set(i, 1);
            i += 1;
        }
        d
    } else if mutation_kind == 6 {
        // set all elements to max
        let n = nums.len();
        let mut d = nums;
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                d.len() == n,
                1 <= n <= 1024,
                exists |k: int| 0 <= k <= 10 && n == pow2(k),
                forall |j: int| 0 <= j < i ==> d[j] == 1_000_000_000i32,
                forall |j: int| i <= j < n as int ==> d[j] == nums[j],
            decreases n - i,
        {
            d.set(i, 1_000_000_000);
            i += 1;
        }
        d
    } else if mutation_kind == 7 && nums.len() >= 2 {
        // swap first two elements
        let mut d = nums;
        let a = d[0];
        let b = d[1];
        d.set(0, b);
        d.set(1, a);
        d
    } else if mutation_kind == 8 {
        // nudge first element up if possible
        let mut d = nums;
        if d[0] < 1_000_000_000 {
            d.set(0, d[0] + 1);
        }
        d
    } else if mutation_kind == 9 {
        // nudge first element down if possible
        let mut d = nums;
        if d[0] > 1 {
            d.set(0, d[0] - 1);
        }
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
    generate_test_case(nums, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(1, 1_000_000_000) as i32);
    }
    v
}

fn pow2_len(k: u32) -> usize {
    1usize << k
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2293);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut total = 0usize;

    let mut emit = |nums: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, total: &mut usize| {
        if *total >= count {
            return;
        }
        let key = format!("{:?}", nums);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::min_max_game(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *total += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![1, 3, 5, 2, 4, 8, 2, 2],
        vec![3],
    ];
    for ex in &examples {
        for mk in 0..=9u8 {
            emit(mutate(ex.clone(), mk), &mut seen, &mut out, &mut total);
        }
    }

    // Hand-crafted seeds: various power-of-2 lengths with interesting values
    let seeds: Vec<Vec<i32>> = vec![
        vec![1],
        vec![1_000_000_000],
        vec![1, 1],
        vec![1_000_000_000, 1_000_000_000],
        vec![1, 1_000_000_000],
        vec![500_000_000, 500_000_000],
        vec![1, 2, 3, 4],
        vec![4, 3, 2, 1],
        vec![1, 1, 1, 1],
        vec![1_000_000_000, 1_000_000_000, 1_000_000_000, 1_000_000_000],
        vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16],
    ];
    for seed_vec in &seeds {
        for mk in 0..=9u8 {
            emit(mutate(seed_vec.clone(), mk), &mut seen, &mut out, &mut total);
        }
    }

    // All valid power-of-2 sizes: k = 0..=10
    let valid_ks: Vec<u32> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

    // Random seeds across all size classes with mutations
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];
    while total < count {
        let k = valid_ks[rng.gen_range_usize(0, valid_ks.len() - 1)];
        let len = pow2_len(k);
        let nums = random_nums(&mut rng, len);
        let mk = mutation_kinds[rng.gen_range_usize(0, mutation_kinds.len() - 1)];
        emit(mutate(nums, mk), &mut seen, &mut out, &mut total);
    }
}
