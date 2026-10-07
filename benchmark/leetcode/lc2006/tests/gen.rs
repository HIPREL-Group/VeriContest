use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, k: i32, mutation_kind: u8) -> (result: (Vec<i32>, i32))
    requires
        1 <= nums.len() <= 200,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
        1 <= k <= 99,
    ensures
        1 <= result.0.len() <= 200,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 100,
        1 <= result.1 <= 99,
{
    if mutation_kind == 0 {
        // identity
        (nums, k)
    } else if mutation_kind == 1 {
        // set first element to 1
        let mut d = nums;
        d.set(0, 1);
        (d, k)
    } else if mutation_kind == 2 {
        // set first element to 100
        let mut d = nums;
        d.set(0, 100);
        (d, k)
    } else if mutation_kind == 3 {
        // set last element to 1
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 1);
        (d, k)
    } else if mutation_kind == 4 {
        // set last element to 100
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 100);
        (d, k)
    } else if mutation_kind == 5 {
        // set all elements to 50
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 200,
                forall|j: int| 0 <= j < i ==> d[j] == 50,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 50);
            i += 1;
        }
        (d, k)
    } else if mutation_kind == 6 && nums.len() < 200 {
        // grow: push element with value k (which is 1..99, so within 1..100)
        let mut d = nums;
        d.push(k);
        (d, k)
    } else if mutation_kind == 7 && nums.len() > 1 {
        // shrink: pop last element
        let mut d = nums;
        d.pop();
        (d, k)
    } else if mutation_kind == 8 && k < 99 {
        // nudge k up
        (nums, k + 1)
    } else if mutation_kind == 9 && k > 1 {
        // nudge k down
        (nums, k - 1)
    } else if mutation_kind == 10 {
        // set k to 1
        (nums, 1)
    } else if mutation_kind == 11 {
        // set k to 99
        (nums, 99)
    } else if mutation_kind == 12 && nums.len() >= 2 {
        // swap first and last elements
        let mut d = nums;
        let last = d.len() - 1;
        let first_val = d[0];
        let last_val = d[last];
        d.set(0, last_val);
        if last > 0 {
            d.set(last, first_val);
        }
        (d, k)
    } else if mutation_kind == 13 {
        // set first element to k (k is 1..99, within 1..100)
        let mut d = nums;
        d.set(0, k);
        (d, k)
    } else if mutation_kind == 14 && nums.len() >= 2 {
        // set first two elements to differ by k (guarantees at least one pair)
        let mut d = nums;
        let base: i32 = 1;
        d.set(0, base);
        if base + k <= 100 {
            d.set(1, base + k);
        } else {
            d.set(1, base);
        }
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

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);

    let mut rng = Rng::new(seed);
    let num_mutations: u8 = 15;
    let mut generated: usize = 0;

    // Example test cases from description.md
    let examples: Vec<(Vec<i32>, i32)> = vec![
        (vec![1, 2, 2, 1], 1),
        (vec![1, 3], 3),
        (vec![3, 2, 1, 5, 4], 2),
    ];
    for (nums, k) in examples {
        let result = Solution::count_k_difference(nums.clone(), k);
        writeln!(out, "{}", json!({"input": {"nums": nums, "k": k}, "output": result})).unwrap();
        generated += 1;
    }

    // Generate diverse test cases
    while generated < count {
        let n: usize = match generated % 5 {
            0 => rng.gen_range_usize(1, 5),     // tiny
            1 => rng.gen_range_usize(1, 10),    // small
            2 => rng.gen_range_usize(11, 50),   // medium
            3 => rng.gen_range_usize(51, 150),  // large
            _ => rng.gen_range_usize(151, 200), // max
        };

        let k = if generated % 5 == 0 {
            *[1i32, 99, 50, 1, 99].get(generated % 5).unwrap()
        } else {
            rng.gen_range_i64(1, 99) as i32
        };

        let nums = random_nums(&mut rng, n);
        let mutation = (rng.next_u64() % num_mutations as u64) as u8;
        let (mutated_nums, mutated_k) = generate_test_case(nums, k, mutation);

        let result = Solution::count_k_difference(mutated_nums.clone(), mutated_k);
        writeln!(out, "{}", json!({
            "input": {"nums": mutated_nums, "k": mutated_k},
            "output": result
        })).unwrap();
        generated += 1;
    }

    eprintln!("Generated {} test cases to {:?}", generated, out_path);
}
