use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= nums.len() <= 20,
        forall|k: int| 0 <= k < nums.len() ==> 0 <= #[trigger] nums[k] <= 10_000_000,
    ensures
        1 <= result.len() <= 20,
        forall|k: int| 0 <= k < result.len() ==> 0 <= #[trigger] result[k] <= 10_000_000,
{
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 {
        // set last element to 0
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 0);
        d
    } else if mutation_kind == 2 {
        // set last element to 10_000_000 (max boundary)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 10_000_000);
        d
    } else if mutation_kind == 3 {
        // set all elements to 0
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 20,
                forall|j: int| 0 <= j < i ==> d[j] == 0,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 0);
            i += 1;
        }
        d
    } else if mutation_kind == 4 {
        // set all elements to 10_000_000
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 20,
                forall|j: int| 0 <= j < i ==> d[j] == 10_000_000,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 10_000_000);
            i += 1;
        }
        d
    } else if mutation_kind == 5 && nums.len() < 20 {
        // grow by one element (push 0)
        let mut d = nums;
        d.push(0);
        d
    } else if mutation_kind == 6 && nums.len() > 1 {
        // shrink by one element (pop)
        let mut d = nums;
        d.pop();
        d
    } else if mutation_kind == 7 {
        // nudge last element up (if < 10_000_000)
        let mut d = nums;
        let last = d.len() - 1;
        if d[last] < 10_000_000 {
            d.set(last, d[last] + 1);
        }
        d
    } else if mutation_kind == 8 {
        // nudge last element down (if > 0)
        let mut d = nums;
        let last = d.len() - 1;
        if d[last] > 0 {
            d.set(last, d[last] - 1);
        }
        d
    } else if mutation_kind == 9 && nums.len() >= 2 {
        // swap first and last elements
        let mut d = nums;
        let last = d.len() - 1;
        let tmp = d[0];
        d.set(0, d[last]);
        d.set(last, tmp);
        d
    } else if mutation_kind == 10 {
        // set first element to 0
        let mut d = nums;
        d.set(0, 0);
        d
    } else if mutation_kind == 11 {
        // set first element to 10_000_000
        let mut d = nums;
        d.set(0, 10_000_000);
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

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(0, 10_000_000) as i32);
    }
    nums
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(486);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut written = 0usize;

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![1, 5, 2],
        vec![1, 5, 233, 7],
    ];
    for nums in &examples {
        let result = Solution::predict_the_winner(nums.clone());
        let line = json!({"input": {"nums": nums}, "output": result});
        let s = line.to_string();
        if seen.insert(s.clone()) {
            writeln!(out, "{}", s).unwrap();
            written += 1;
        }
    }

    // Boundary / special cases
    let specials: Vec<Vec<i32>> = vec![
        vec![0],
        vec![10_000_000],
        vec![0, 0],
        vec![1, 1],
        vec![10_000_000, 10_000_000],
        vec![0, 10_000_000],
        vec![10_000_000, 0],
        vec![0; 20],
        vec![10_000_000; 20],
        vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20],
    ];
    for nums in &specials {
        let result = Solution::predict_the_winner(nums.clone());
        let line = json!({"input": {"nums": nums}, "output": result});
        let s = line.to_string();
        if seen.insert(s.clone()) {
            writeln!(out, "{}", s).unwrap();
            written += 1;
        }
    }

    let num_mutations: u8 = 12;

    while written < count {
        // Size classes for array length (1..=20)
        let n: usize = match written % 5 {
            0 => rng.gen_range_usize(1, 3),    // tiny
            1 => rng.gen_range_usize(1, 5),    // small
            2 => rng.gen_range_usize(6, 10),   // medium
            3 => rng.gen_range_usize(11, 15),  // large
            _ => rng.gen_range_usize(16, 20),  // max
        };

        let base_nums = random_nums(&mut rng, n);
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let nums = mutate(base_nums, mk);
        let result = Solution::predict_the_winner(nums.clone());
        let line = json!({"input": {"nums": nums}, "output": result});
        let s = line.to_string();
        if seen.insert(s.clone()) {
            writeln!(out, "{}", s).unwrap();
            written += 1;
        }
    }

    eprintln!("Wrote {} test cases to {:?}", written, out_path);
}
