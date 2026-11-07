use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= nums.len() <= 100,
        forall|i: int| 0 <= i < nums.len() ==> -1000 <= #[trigger] nums[i] <= 1000,
    ensures
        1 <= result.len() <= 100,
        forall|i: int| 0 <= i < result.len() ==> -1000 <= #[trigger] result[i] <= 1000,
{
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 {
        // set first element to 0
        let mut d = nums;
        d.set(0, 0);
        d
    } else if mutation_kind == 2 {
        // set all elements to 0
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 100,
                forall|j: int| 0 <= j < i ==> d[j] == 0,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 0);
            i += 1;
        }
        d
    } else if mutation_kind == 3 && nums.len() < 100 {
        // grow by one element (push 0)
        let mut d = nums;
        d.push(0);
        d
    } else if mutation_kind == 4 && nums.len() > 1 {
        // shrink by one element (pop)
        let mut d = nums;
        d.pop();
        d
    } else if mutation_kind == 5 {
        // set first element to 1000 (max boundary)
        let mut d = nums;
        d.set(0, 1000);
        d
    } else if mutation_kind == 6 {
        // set first element to -1000 (min boundary)
        let mut d = nums;
        d.set(0, -1000);
        d
    } else if mutation_kind == 7 {
        // nudge first element up if < 1000
        let mut d = nums;
        if d[0] < 1000 {
            d.set(0, d[0] + 1);
        }
        d
    } else if mutation_kind == 8 {
        // nudge first element down if > -1000
        let mut d = nums;
        if d[0] > -1000 {
            d.set(0, d[0] - 1);
        }
        d
    } else if mutation_kind == 9 && nums.len() >= 2 {
        // swap first two elements
        let mut d = nums;
        let a = d[0];
        let b = d[1];
        d.set(0, b);
        d.set(1, a);
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

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(-1000, 1000) as i32);
    }
    nums
}

fn mutate(nums: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(nums, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);

    let mut rng = Rng::new(seed);
    let mut generated = 0;

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![2, 3, -1, 8, 4],
        vec![1, -1, 4],
        vec![2, 5],
    ];

    for ex in &examples {
        if generated >= count { break; }
        let nums = ex.clone();
        let result = Solution::find_middle_index(nums.clone());
        writeln!(out, "{}", json!({
            "input": {"nums": nums},
            "output": result
        })).unwrap();
        generated += 1;
    }

    // Deterministic boundary cases
    let boundary_cases: Vec<Vec<i32>> = vec![
        vec![0],               // single element
        vec![1000],            // single max
        vec![-1000],           // single min
        vec![0; 100],          // max length, all zeros
        vec![1000; 1],         // single boundary
    ];

    for bc in &boundary_cases {
        if generated >= count { break; }
        let nums = bc.clone();
        let result = Solution::find_middle_index(nums.clone());
        writeln!(out, "{}", json!({
            "input": {"nums": nums},
            "output": result
        })).unwrap();
        generated += 1;
    }

    // Random test cases with diverse sizes and mutations
    let num_mutations: u8 = 10;

    while generated < count {
        // Size classes
        let n: usize = match generated % 5 {
            0 => rng.gen_range_usize(1, 3),        // tiny
            1 => rng.gen_range_usize(1, 10),       // small
            2 => rng.gen_range_usize(11, 30),      // medium
            3 => rng.gen_range_usize(31, 70),      // large
            _ => rng.gen_range_usize(71, 100),     // max
        };

        let base = random_nums(&mut rng, n);
        let mutation_kind = (rng.next_u64() % num_mutations as u64) as u8;
        let nums = mutate(base, mutation_kind);
        let result = Solution::find_middle_index(nums.clone());
        writeln!(out, "{}", json!({
            "input": {"nums": nums},
            "output": result
        })).unwrap();
        generated += 1;
    }

    eprintln!("Generated {} test cases to {}", generated, out_path.display());
}
