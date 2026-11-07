use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    nums: Vec<i32>,
    k: i32,
    multiplier: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32, i32))
    requires
        1 <= nums.len() <= 100,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
        1 <= k <= 10,
        1 <= multiplier <= 5,
    ensures
        1 <= result.0.len() <= 100,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 100,
        1 <= result.1 <= 10,
        1 <= result.2 <= 5,
{
    if mutation_kind == 0 {
        // identity
        (nums, k, multiplier)
    } else if mutation_kind == 1 {
        // set first element to 1 (min boundary)
        let mut d = nums;
        d.set(0, 1);
        (d, k, multiplier)
    } else if mutation_kind == 2 {
        // set first element to 100 (max boundary)
        let mut d = nums;
        d.set(0, 100);
        (d, k, multiplier)
    } else if mutation_kind == 3 {
        // set all elements to 1
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 100,
                forall|j: int| 0 <= j < i ==> d[j] == 1i32,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 1);
            i += 1;
        }
        (d, k, multiplier)
    } else if mutation_kind == 4 {
        // set all elements to 100
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 100,
                forall|j: int| 0 <= j < i ==> d[j] == 100i32,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 100);
            i += 1;
        }
        (d, k, multiplier)
    } else if mutation_kind == 5 && nums.len() < 100 {
        // grow array by one element
        let mut d = nums;
        d.push(1);
        (d, k, multiplier)
    } else if mutation_kind == 6 && nums.len() > 1 {
        // shrink array by one element
        let mut d = nums;
        d.pop();
        (d, k, multiplier)
    } else if mutation_kind == 7 {
        // nudge last element up (if < 100)
        let mut d = nums;
        let last = d.len() - 1;
        if d[last] < 100 {
            d.set(last, d[last] + 1);
        }
        (d, k, multiplier)
    } else if mutation_kind == 8 {
        // nudge last element down (if > 1)
        let mut d = nums;
        let last = d.len() - 1;
        if d[last] > 1 {
            d.set(last, d[last] - 1);
        }
        (d, k, multiplier)
    } else if mutation_kind == 9 {
        // set k to 1 (min boundary)
        (nums, 1, multiplier)
    } else if mutation_kind == 10 {
        // set k to 10 (max boundary)
        (nums, 10, multiplier)
    } else if mutation_kind == 11 {
        // set multiplier to 1 (identity multiplier)
        (nums, k, 1)
    } else if mutation_kind == 12 {
        // set multiplier to 5 (max boundary)
        (nums, k, 5)
    } else {
        // fallback
        (nums, k, multiplier)
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

fn mutate(nums: Vec<i32>, k: i32, multiplier: i32, mutation_kind: u8) -> (Vec<i32>, i32, i32) {
    generate_test_case(nums, k, multiplier, mutation_kind)
}

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(1, 100) as i32);
    }
    nums
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(3264);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>, k: i32, multiplier: i32,
                    seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>,
                    count: &mut usize| {
        if *count >= target {
            return;
        }
        let key = format!("{:?}_{}_{}", nums, k, multiplier);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::get_final_state(nums.clone(), k, multiplier);
        writeln!(out, "{}", json!({
            "input": {"nums": nums, "k": k, "multiplier": multiplier},
            "output": output
        })).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<(Vec<i32>, i32, i32)> = vec![
        (vec![2, 1, 3, 5, 6], 5, 2),
        (vec![1, 2], 3, 4),
    ];
    for (nums, k, m) in &examples {
        emit(nums.clone(), *k, *m, &mut seen, &mut out, &mut count);
    }

    // Curated seeds with structural diversity
    let seed_arrays: Vec<Vec<i32>> = vec![
        vec![1],
        vec![100],
        vec![1, 1, 1],
        vec![100, 100, 100],
        vec![1, 100],
        vec![50, 50, 50, 50],
        vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
        vec![10, 9, 8, 7, 6, 5, 4, 3, 2, 1],
    ];
    let k_vals: Vec<i32> = vec![1, 5, 10];
    let m_vals: Vec<i32> = vec![1, 2, 3, 5];
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12];

    // Apply mutations to curated seeds across k and multiplier values
    for seed_arr in &seed_arrays {
        for &k in &k_vals {
            for &m in &m_vals {
                for &mk in &mutation_kinds {
                    if count >= target { break; }
                    let (nums, k_out, m_out) = mutate(seed_arr.clone(), k, m, mk);
                    emit(nums, k_out, m_out, &mut seen, &mut out, &mut count);
                }
            }
        }
    }

    // Random inputs with random mutations
    while count < target {
        let len = match count % 5 {
            0 => rng.gen_range_usize(1, 3),       // tiny
            1 => rng.gen_range_usize(1, 10),      // small
            2 => rng.gen_range_usize(11, 30),     // medium
            3 => rng.gen_range_usize(31, 70),     // large
            _ => rng.gen_range_usize(71, 100),    // max
        };
        let nums = random_nums(&mut rng, len);
        let k = rng.gen_range_i64(1, 10) as i32;
        let m = rng.gen_range_i64(1, 5) as i32;
        let mk = rng.gen_range_usize(0, 12) as u8;
        let (nums_out, k_out, m_out) = mutate(nums, k, m, mk);
        emit(nums_out, k_out, m_out, &mut seen, &mut out, &mut count);
    }
}
