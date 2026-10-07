use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    vals: Vec<i32>,
    original: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= vals.len() <= 1000,
        forall |i: int| 0 <= i < vals.len() ==> 1 <= #[trigger] vals[i] <= 1000,
        1 <= original <= 1000,
    ensures
        1 <= result.0.len() <= 1000,
        forall |i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 1000,
        1 <= result.1 <= 1000,
{
    if mutation_kind == 0 {
        // Identity
        (vals, original)
    } else if mutation_kind == 1 {
        // Ensure original appears in nums
        let mut nums = vals;
        nums.set(0, original);
        (nums, original)
    } else if mutation_kind == 2 && original <= 500 {
        // Ensure original and original*2 both appear
        let mut nums = vals;
        nums.set(0, original);
        if nums.len() >= 2 {
            let doubled = original * 2;
            assert(1 <= doubled <= 1000);
            nums.set(1, doubled);
        }
        (nums, original)
    } else if mutation_kind == 3 && vals.len() >= 2 {
        // Shrink array by one
        let mut nums = vals;
        let _removed = nums.pop();
        (nums, original)
    } else if mutation_kind == 4 && vals.len() < 1000 {
        // Grow array by pushing original
        let mut nums = vals;
        nums.push(original);
        (nums, original)
    } else if mutation_kind == 5 {
        // Set all elements to original
        let mut nums = vals;
        let len = nums.len();
        let mut j: usize = 0;
        while j < len
            invariant
                len == nums.len(),
                0 <= j <= len,
                1 <= original <= 1000,
                forall |k: int| 0 <= k < j ==> #[trigger] nums[k] == original,
                forall |k: int| j <= k < len ==> 1 <= #[trigger] nums[k] <= 1000,
            decreases len - j,
        {
            nums.set(j, original);
            j += 1;
        }
        (nums, original)
    } else if mutation_kind == 6 && original < 1000 {
        // Nudge original up
        (vals, (original + 1) as i32)
    } else if mutation_kind == 7 && original > 1 {
        // Nudge original down
        (vals, (original - 1) as i32)
    } else if mutation_kind == 8 {
        // Boundary: original = 1
        (vals, 1i32)
    } else if mutation_kind == 9 {
        // Boundary: original = 1000
        (vals, 1000i32)
    } else if mutation_kind == 10 {
        // Set first element to 1 (min boundary)
        let mut nums = vals;
        nums.set(0, 1i32);
        (nums, original)
    } else if mutation_kind == 11 {
        // Set first element to 1000 (max boundary)
        let mut nums = vals;
        nums.set(0, 1000i32);
        (nums, original)
    } else {
        // Fallback: identity
        (vals, original)
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

    fn gen_u8(&mut self) -> u8 {
        (self.next_u64() % 256) as u8
    }
}

struct Solution;
include!("../code.rs");

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut generated = 0usize;

    // Example inputs from description.md
    let examples: Vec<(Vec<i32>, i32)> = vec![
        (vec![5, 3, 6, 1, 12], 3),
        (vec![2, 7, 9], 4),
    ];

    for (nums, original) in &examples {
        if generated >= count { break; }
        let key = format!("{:?}:{}", nums, original);
        if seen.insert(key) {
            let output = Solution::find_final_value(nums.clone(), *original);
            writeln!(out, "{}", json!({
                "input": {"nums": nums, "original": original},
                "output": output
            })).unwrap();
            generated += 1;
        }
    }

    // Structured seeds: iterate size classes x mutation kinds
    let size_classes: Vec<usize> = vec![1, 2, 5, 10, 50, 100, 500, 1000];
    for &n in &size_classes {
        for mk in 0..=11u8 {
            if generated >= count { break; }
            let mut vals: Vec<i32> = Vec::new();
            for _ in 0..n {
                vals.push(rng.gen_range_i64(1, 1000) as i32);
            }
            let original = rng.gen_range_i64(1, 1000) as i32;
            let (nums, orig) = generate_test_case(vals, original, mk);
            let key = format!("{:?}:{}", nums, orig);
            if seen.insert(key) {
                let output = Solution::find_final_value(nums.clone(), orig);
                writeln!(out, "{}", json!({
                    "input": {"nums": nums, "original": orig},
                    "output": output
                })).unwrap();
                generated += 1;
            }
        }
        if generated >= count { break; }
    }

    // Fill remaining with random inputs
    while generated < count {
        let n = match generated % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 500),
            _ => rng.gen_range_usize(501, 1000),
        };
        let mut vals: Vec<i32> = Vec::new();
        for _ in 0..n {
            let v = if generated % 5 == 0 {
                *[1i32, 1000, 500, 2, 999].iter().nth(
                    rng.gen_range_usize(0, 4)
                ).unwrap()
            } else {
                rng.gen_range_i64(1, 1000) as i32
            };
            vals.push(v);
        }
        let original = if generated % 7 == 0 {
            *[1i32, 2, 500, 999, 1000].iter().nth(
                rng.gen_range_usize(0, 4)
            ).unwrap()
        } else {
            rng.gen_range_i64(1, 1000) as i32
        };
        let mk = rng.gen_u8() % 12;
        let (nums, orig) = generate_test_case(vals, original, mk);
        let key = format!("{:?}:{}", nums, orig);
        if seen.insert(key) {
            let output = Solution::find_final_value(nums.clone(), orig);
            writeln!(out, "{}", json!({
                "input": {"nums": nums, "original": orig},
                "output": output
            })).unwrap();
            generated += 1;
        }
    }
}
