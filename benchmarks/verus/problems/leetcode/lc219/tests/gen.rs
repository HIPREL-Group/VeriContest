use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    base: &Vec<i32>,
    k: i32,
    dup_src: usize,
    dup_dst: usize,
    mutation_kind: u8,
) -> (nums: Vec<i32>)
    requires
        1 <= base.len() <= 10_000,
        forall|i: int| 0 <= i < base.len() ==>
            -1_000_000_000 <= #[trigger] base[i] <= 1_000_000_000,
        0 <= k <= 10_000,
        dup_src < base.len(),
        dup_dst < base.len(),
        dup_dst >= 1,
    ensures
        1 <= nums.len() <= 10_000,
        forall|i: int| 1 <= i < nums.len() ==>
            -1_000_000_000 <= #[trigger] nums[i] <= 1_000_000_000,
        0 <= k <= 10_000,
{
    let mut nums: Vec<i32> = Vec::new();
    let mut pos: usize = 0;

    while pos < base.len()
        invariant
            0 <= pos <= base.len(),
            nums.len() == pos,
            1 <= base.len() <= 10_000,
            forall|i: int| 0 <= i < base.len() ==>
                -1_000_000_000 <= #[trigger] base[i] <= 1_000_000_000,
            forall|i: int| 0 <= i < pos as int ==>
                nums[i] == base[i],
            forall|i: int| 0 <= i < pos as int ==>
                -1_000_000_000 <= #[trigger] nums[i] <= 1_000_000_000,
        decreases base.len() - pos,
    {
        nums.push(base[pos]);
        pos = pos + 1;
    }

    if mutation_kind == 0u8 {
        // Identity: return copy of base
    } else if mutation_kind == 1u8 {
        // Create a nearby duplicate: set nums[dup_dst] = nums[dup_src]
        let val = nums[dup_src];
        nums.set(dup_dst, val);
    } else if mutation_kind == 2u8 && nums.len() >= 2 {
        // Swap first two elements
        let v0 = nums[0];
        let v1 = nums[1];
        nums.set(0, v1);
        nums.set(1, v0);
    } else if mutation_kind == 3u8 {
        // Set element at dup_dst to 0
        nums.set(dup_dst, 0i32);
    } else if mutation_kind == 4u8 {
        // Set element at dup_dst to max boundary
        nums.set(dup_dst, 1_000_000_000i32);
    } else if mutation_kind == 5u8 {
        // Set element at dup_dst to min boundary
        nums.set(dup_dst, -1_000_000_000i32);
    } else if mutation_kind == 6u8 && nums.len() >= 2 {
        // Set two adjacent elements to same value (guaranteed nearby dup)
        let val = nums[dup_src];
        nums.set(dup_dst, val);
        if dup_dst + 1 < nums.len() {
            nums.set(dup_dst + 1, val);
        }
    } else if mutation_kind == 7u8 {
        // Nudge element at dup_dst by +1 (if in range)
        let val = nums[dup_dst];
        if val < 1_000_000_000i32 {
            nums.set(dup_dst, val + 1);
        }
    } else if mutation_kind == 8u8 {
        // Nudge element at dup_dst by -1 (if in range)
        let val = nums[dup_dst];
        if val > -1_000_000_000i32 {
            nums.set(dup_dst, val - 1);
        }
    } else {
        // Fallback: identity
    }

    proof {
        assert(nums.len() == base.len());
        assert(1 <= nums.len() <= 10_000);
    }

    nums
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

extern crate serde_json;
use serde_json::json;

struct Solution;
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
    let mut generated: usize = 0;

    // Example test cases from description.md
    let examples: Vec<(Vec<i32>, i32)> = vec![
        (vec![1, 2, 3, 1], 3),
        (vec![1, 0, 1, 1], 1),
        (vec![1, 2, 3, 1, 2, 3], 2),
    ];

    for (nums, k) in &examples {
        let result = Solution::contains_nearby_duplicate(nums.clone(), *k);
        writeln!(out, "{}", json!({
            "input": {"nums": nums, "k": k},
            "output": result
        })).unwrap();
        generated += 1;
    }

    // Generate random test cases
    while generated < count {
        // Size classes
        let n: usize = match generated % 5 {
            0 => rng.gen_range_usize(2, 5),       // tiny
            1 => rng.gen_range_usize(2, 10),      // small
            2 => rng.gen_range_usize(11, 100),    // medium
            3 => rng.gen_range_usize(101, 1000),  // large
            _ => rng.gen_range_usize(1001, 10000), // max
        };

        // Build base array
        let mut base: Vec<i32> = Vec::new();
        for _ in 0..n {
            let val = if generated % 5 == 0 {
                // Boundary values ~20% of the time
                match rng.gen_range_usize(0, 4) {
                    0 => -1_000_000_000i64,
                    1 => 1_000_000_000i64,
                    2 => 0i64,
                    3 => 1i64,
                    _ => -1i64,
                }
            } else {
                rng.gen_range_i64(-1_000_000_000, 1_000_000_000)
            } as i32;
            base.push(val);
        }

        // k value
        let k: i32 = if generated % 7 == 0 {
            0
        } else if generated % 7 == 1 {
            10_000
        } else if generated % 7 == 2 {
            1
        } else if generated % 7 == 3 {
            n as i32
        } else {
            rng.gen_range_i64(0, 10_000) as i32
        };

        let dup_src = rng.gen_range_usize(0, n - 1);
        let dup_dst = rng.gen_range_usize(1, n - 1);
        // Ensure dup_dst >= 1 (already guaranteed by gen_range_usize(1, ...))

        let mutation_kind = rng.gen_range_usize(0, 8) as u8;

        let nums = generate_test_case(&base, k, dup_src, dup_dst, mutation_kind);

        let result = Solution::contains_nearby_duplicate(nums.clone(), k);
        writeln!(out, "{}", json!({
            "input": {"nums": nums, "k": k},
            "output": result
        })).unwrap();
        generated += 1;
    }

    eprintln!("Generated {} test cases to {:?}", generated, out_path);
}
