use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    nums: Vec<i32>,
    left: i32,
    right: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32, i32, i32))
    requires
        1 <= nums.len() <= 1000,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
        1 <= left <= right <= (nums@.len() * (nums@.len() + 1) / 2),
    ensures
        result.1 == result.0@.len(),
        1 <= result.0@.len() <= 1000,
        forall |i: int| 0 <= i < result.0@.len() ==> 1 <= #[trigger] result.0@[i] <= 100,
        1 <= result.2 <= result.3 <= result.1 * (result.1 + 1) / 2,
{
    let n = nums.len() as i32;

    if mutation_kind == 0 {
        (nums, n, left, right)
    } else if mutation_kind == 1 {
        let mut d = nums;
        d.set(0, 1);
        (d, n, left, right)
    } else if mutation_kind == 2 {
        let mut d = nums;
        d.set(0, 100);
        (d, n, left, right)
    } else if mutation_kind == 3 {
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 1);
        (d, n, left, right)
    } else if mutation_kind == 4 {
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 100);
        (d, n, left, right)
    } else if mutation_kind == 5 && nums[0] < 100 {
        let mut d = nums;
        let v = d[0] + 1;
        d.set(0, v);
        (d, n, left, right)
    } else if mutation_kind == 6 {
        (nums, n, left, left)
    } else if mutation_kind == 7 {
        (nums, n, 1, right)
    } else {
        (nums, n, left, right)
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
        let (lo, hi) = if lo <= hi { (lo, hi) } else { (hi, lo) };
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let (lo, hi) = if lo <= hi { (lo, hi) } else { (hi, lo) };
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

struct Solution;
include!("../code.rs");

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
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1508);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>, n: i32, left: i32, right: i32,
                     seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>,
                     count: &mut usize| {
        if *count >= target {
            return;
        }
        let key = format!("{:?},{},{},{}", nums, n, left, right);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::range_sum(nums.clone(), n, left, right);
        writeln!(out, "{}", json!({
            "input": {"nums": nums, "n": n, "left": left, "right": right},
            "output": output
        })).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<(Vec<i32>, i32, i32, u8)> = vec![
        (vec![1, 2, 3, 4], 1, 5, 0),
        (vec![1, 2, 3, 4], 3, 4, 0),
        (vec![1, 2, 3, 4], 1, 10, 0),
    ];
    for (nums, left, right, mk) in examples {
        let (r_nums, r_n, r_left, r_right) = generate_test_case(nums, left, right, mk);
        emit(r_nums, r_n, r_left, r_right, &mut seen, &mut out, &mut count);
    }

    // Seed arrays × all mutation kinds
    let seed_arrays: Vec<Vec<i32>> = vec![
        vec![1],
        vec![100],
        vec![1, 1],
        vec![100, 100],
        vec![50],
        vec![1, 2, 3],
        vec![1, 100],
        vec![50, 50, 50, 50],
        vec![1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
        vec![100, 100, 100, 100, 100],
    ];
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7];

    for seed_arr in &seed_arrays {
        let n = seed_arr.len() as i64;
        let max_pos = (n * (n + 1) / 2) as i32;
        for &mk in &mutation_kinds {
            let (r_nums, r_n, r_left, r_right) =
                generate_test_case(seed_arr.clone(), 1, max_pos, mk);
            emit(r_nums, r_n, r_left, r_right, &mut seen, &mut out, &mut count);
        }
    }

    // Random inputs with mutations across diverse size classes
    let mut _attempts = 0usize;
    while count < target {
        _attempts += 1; if _attempts > 10000 { break; }
        let n: usize = match count % 5 {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 30),
            3 => rng.gen_range_usize(31, 60),
            _ => rng.gen_range_usize(61, 100),
        };
        let nums = random_nums(&mut rng, n);
        let max_pos = (n as i64 * (n as i64 + 1) / 2) as i32;
        let left = rng.gen_range_i64(1, max_pos as i64) as i32;
        let right = rng.gen_range_i64(left as i64, max_pos as i64) as i32;
        let mk = rng.gen_range_usize(0, 7) as u8;

        let (r_nums, r_n, r_left, r_right) =
            generate_test_case(nums, left, right, mk);
        emit(r_nums, r_n, r_left, r_right, &mut seen, &mut out, &mut count);
    }
}
