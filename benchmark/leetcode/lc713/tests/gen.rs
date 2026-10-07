use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    seeds: &Vec<i32>,
    k: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= seeds.len() <= 30_000,
        forall|i: int| 0 <= i < seeds.len() ==> 1 <= #[trigger] seeds[i] <= 1000,
        0 <= k <= 1_000_000,
    ensures
        1 <= result.0.len() <= 30_000,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 1000,
        0 <= result.1 <= 1_000_000,
{
    let mut nums: Vec<i32> = Vec::new();
    let mut idx: usize = 0;
    while idx < seeds.len()
        invariant
            0 <= idx <= seeds.len(),
            nums.len() == idx,
            1 <= seeds.len() <= 30_000,
            forall|i: int| 0 <= i < seeds.len() ==> 1 <= #[trigger] seeds[i] <= 1000,
            forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
        decreases seeds.len() - idx,
    {
        nums.push(seeds[idx]);
        idx = idx + 1;
    }

    if mutation_kind == 0 {
        // identity
        (nums, k)
    } else if mutation_kind == 1 {
        // set all elements to 1
        let mut out: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < nums.len()
            invariant
                0 <= j <= nums.len(),
                out.len() == j,
                1 <= nums.len() <= 30_000,
                forall|i: int| 0 <= i < out.len() ==> #[trigger] out[i] == 1i32,
            decreases nums.len() - j,
        {
            out.push(1i32);
            j = j + 1;
        }
        assert forall|i: int| 0 <= i < out.len() implies 1 <= #[trigger] out[i] <= 1000 by {
            assert(out[i] == 1i32);
        };
        (out, k)
    } else if mutation_kind == 2 {
        // set all elements to 1000
        let mut out: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < nums.len()
            invariant
                0 <= j <= nums.len(),
                out.len() == j,
                1 <= nums.len() <= 30_000,
                forall|i: int| 0 <= i < out.len() ==> #[trigger] out[i] == 1000i32,
            decreases nums.len() - j,
        {
            out.push(1000i32);
            j = j + 1;
        }
        assert forall|i: int| 0 <= i < out.len() implies 1 <= #[trigger] out[i] <= 1000 by {
            assert(out[i] == 1000i32);
        };
        (out, k)
    } else if mutation_kind == 3 {
        // k = 0
        (nums, 0i32)
    } else if mutation_kind == 4 {
        // k = 1_000_000
        (nums, 1_000_000i32)
    } else if mutation_kind == 5 {
        // k = 1 (no subarray qualifies since all elements >= 1)
        (nums, 1i32)
    } else if mutation_kind == 6 && nums.len() >= 2 {
        // shrink by removing last element
        let mut out: Vec<i32> = Vec::new();
        let new_len = nums.len() - 1;
        let mut j: usize = 0;
        while j < new_len
            invariant
                0 <= j <= new_len,
                out.len() == j,
                new_len == nums.len() - 1,
                nums.len() >= 2,
                1 <= nums.len() <= 30_000,
                forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
                forall|i: int| 0 <= i < out.len() ==> 1 <= #[trigger] out[i] <= 1000,
            decreases new_len - j,
        {
            out.push(nums[j]);
            j = j + 1;
        }
        (out, k)
    } else if mutation_kind == 7 && nums.len() < 30_000 {
        // grow by appending element 1
        nums.push(1i32);
        assert forall|i: int| 0 <= i < nums.len() implies 1 <= #[trigger] nums[i] <= 1000 by {
            if i < nums.len() - 1 {
            } else {
                assert(nums[i] == 1i32);
            }
        };
        (nums, k)
    } else if mutation_kind == 8 {
        // nudge first element: set to 1
        if nums.len() >= 1 {
            nums.set(0, 1i32);
            assert forall|i: int| 0 <= i < nums.len() implies 1 <= #[trigger] nums[i] <= 1000 by {
                if i == 0 {
                    assert(nums[i] == 1i32);
                }
            };
        }
        (nums, k)
    } else if mutation_kind == 9 {
        // nudge first element: set to 1000
        if nums.len() >= 1 {
            nums.set(0, 1000i32);
            assert forall|i: int| 0 <= i < nums.len() implies 1 <= #[trigger] nums[i] <= 1000 by {
                if i == 0 {
                    assert(nums[i] == 1000i32);
                }
            };
        }
        (nums, k)
    } else if mutation_kind == 10 && nums.len() >= 2 {
        // swap first two elements
        let a = nums[0];
        let b = nums[1];
        nums.set(0, b);
        nums.set(1, a);
        assert forall|i: int| 0 <= i < nums.len() implies 1 <= #[trigger] nums[i] <= 1000 by {
            if i == 0 {
                assert(nums[i] == b);
            } else if i == 1 {
                assert(nums[i] == a);
            }
        };
        (nums, k)
    } else {
        // fallback: identity
        (nums, k)
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

struct Solution;
include!("../code.rs");

fn random_seeds(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = Vec::new();
    for _ in 0..n {
        v.push(rng.gen_range_i64(1, 1000) as i32);
    }
    v
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count_goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    macro_rules! emit {
        ($seeds:expr, $k:expr, $mk:expr) => {
            if count < count_goal {
                let seeds_val: Vec<i32> = $seeds;
                let k_val: i32 = $k;
                let mk_val: u8 = $mk;
                let (nums_out, k_out) = generate_test_case(&seeds_val, k_val, mk_val);
                let result = Solution::num_subarray_product_less_than_k(
                    nums_out.clone(), k_out,
                );
                let line = json!({
                    "input": {"nums": nums_out, "k": k_out},
                    "output": result
                }).to_string();
                if seen.insert(line.clone()) {
                    writeln!(out, "{}", line).unwrap();
                    count += 1;
                }
            }
        };
    }

    // ---- LeetCode examples ----
    emit!(vec![10, 5, 2, 6], 100, 0);
    emit!(vec![1, 2, 3], 0, 0);

    // ---- Boundary k values with example array ----
    emit!(vec![10, 5, 2, 6], 1, 0);
    emit!(vec![10, 5, 2, 6], 1_000_000, 0);

    // ---- Single element cases ----
    emit!(vec![1], 1, 0);
    emit!(vec![1], 2, 0);
    emit!(vec![1000], 1000, 0);
    emit!(vec![1000], 1001, 0);
    emit!(vec![1], 0, 0);

    // ---- All-ones array ----
    emit!(vec![1; 10], 2, 0);
    emit!(vec![1; 100], 2, 0);

    // ---- All mutations on a small array ----
    for mk in 0u8..=10 {
        emit!(vec![5, 10, 20, 3, 7], 50, mk);
    }

    // ---- Random test cases with diverse sizes and mutations ----
    while count < count_goal {
        let n: usize = match count % 5 {
            0 => rng.gen_range_usize(1, 5),       // tiny
            1 => rng.gen_range_usize(1, 10),      // small
            2 => rng.gen_range_usize(11, 100),    // medium
            3 => rng.gen_range_usize(101, 1000),  // large
            _ => rng.gen_range_usize(1001, 5000), // big
        };

        let seeds = random_seeds(&mut rng, n);

        // Diverse k values
        let k: i32 = match count % 7 {
            0 => 0,
            1 => 1,
            2 => rng.gen_range_i64(2, 100) as i32,
            3 => rng.gen_range_i64(100, 10_000) as i32,
            4 => rng.gen_range_i64(10_000, 1_000_000) as i32,
            5 => 1_000_000,
            _ => rng.gen_range_i64(0, 1_000_000) as i32,
        };

        let mk = (rng.next_u64() % 11) as u8;
        emit!(seeds, k, mk);
    }

    eprintln!("Generated {} test cases", count);
}
