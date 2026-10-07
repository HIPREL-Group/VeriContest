use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        nums.len() >= 1,
        nums.len() <= 5000,
        forall|i: int| 0 <= i < nums.len() ==> -1000 <= #[trigger] nums[i] <= 1000,
    ensures
        result.len() >= 1,
        result.len() <= 5000,
        forall|i: int| 0 <= i < result.len() ==> -1000 <= #[trigger] result[i] <= 1000,
{
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 {
        // set all elements to 0 (constant arithmetic sequence)
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 5000,
                forall|j: int| 0 <= j < i ==> d[j] == 0i32,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 0);
            i += 1;
        }
        d
    } else if mutation_kind == 2 && nums.len() < 5000 {
        // grow array by one element (push 0)
        let mut d = nums;
        d.push(0);
        assert(d.len() <= 5000);
        assert(forall|j: int| 0 <= j < nums.len() as int ==> d[j] == nums[j]);
        d
    } else if mutation_kind == 3 && nums.len() > 1 {
        // shrink array by one element (pop)
        let mut d = nums;
        d.pop();
        d
    } else if mutation_kind == 4 {
        // set last element to 0
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 0);
        d
    } else if mutation_kind == 5 {
        // nudge first element up (if < 1000)
        let mut d = nums;
        if d[0] < 1000 {
            d.set(0, (d[0] as i32) + 1);
        }
        d
    } else if mutation_kind == 6 {
        // nudge first element down (if > -1000)
        let mut d = nums;
        if d[0] > -1000 {
            d.set(0, (d[0] as i32) - 1);
        }
        d
    } else if mutation_kind == 7 && nums.len() >= 2 {
        // swap first and last elements
        let mut d = nums;
        let last = d.len() - 1;
        let tmp = d[0];
        d.set(0, d[last]);
        d.set(last, tmp);
        d
    } else if mutation_kind == 8 {
        // set first element to boundary -1000
        let mut d = nums;
        d.set(0, -1000);
        d
    } else if mutation_kind == 9 {
        // set first element to boundary 1000
        let mut d = nums;
        d.set(0, 1000);
        d
    } else {
        // fallback: identity
        nums
    }
}

} // verus!

extern crate serde_json;
use serde_json::json;

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

include!("../code.rs");

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    use std::io::Write;

    let mut rng = Rng::new(seed);
    let mut case_idx: usize = 0;

    // Example test cases from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![1, 2, 3, 4],
        vec![1],
    ];
    for nums in &examples {
        let result = number_of_arithmetic_slices(nums.clone());
        writeln!(out, "{}", json!({
            "input": {"nums": nums},
            "output": result
        })).unwrap();
        case_idx += 1;
    }

    // Generate random test cases
    while case_idx < count {
        // Size classes
        let n: usize = match case_idx % 5 {
            0 => rng.gen_range_usize(1, 3),       // tiny
            1 => rng.gen_range_usize(1, 10),      // small
            2 => rng.gen_range_usize(11, 100),    // medium
            3 => rng.gen_range_usize(101, 1000),  // large
            _ => rng.gen_range_usize(1001, 5000), // max
        };

        // Build array
        let mut nums: Vec<i32> = Vec::with_capacity(n);
        // Use different value strategies for diversity
        let val_strategy = case_idx % 4;
        for j in 0..n {
            let v: i32 = match val_strategy {
                0 => {
                    // fully random values
                    rng.gen_range_i64(-1000, 1000) as i32
                }
                1 => {
                    // arithmetic progression (to create many slices)
                    let diff = rng.gen_range_i64(-5, 5) as i32;
                    let base = rng.gen_range_i64(-500, 500) as i32;
                    let v = base as i64 + (diff as i64) * (j as i64);
                    v.max(-1000).min(1000) as i32
                }
                2 => {
                    // boundary values mixed in
                    if j % 5 == 0 {
                        *[-1000i32, 1000, 0, 1, -1].get(rng.gen_range_usize(0, 4)).unwrap()
                    } else {
                        rng.gen_range_i64(-1000, 1000) as i32
                    }
                }
                _ => {
                    // constant value (all same -> many arithmetic slices)
                    rng.gen_range_i64(-1000, 1000) as i32
                }
            };
            nums.push(v);
        }

        let mutation_kind: u8 = rng.gen_range_usize(0, 9) as u8;
        let mutated = generate_test_case(nums, mutation_kind);

        let result = number_of_arithmetic_slices(mutated.clone());
        writeln!(out, "{}", json!({
            "input": {"nums": mutated},
            "output": result
        })).unwrap();

        case_idx += 1;
    }
}
