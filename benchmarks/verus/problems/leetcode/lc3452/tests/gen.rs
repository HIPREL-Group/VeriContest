use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    nums: Vec<i32>,
    k: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32))
    requires
        2 <= nums.len() <= 100,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
        1 <= k,
        k as int <= nums.len() as int / 2,
    ensures
        2 <= result.0.len() <= 100,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 1000,
        1 <= result.1,
        result.1 as int <= result.0.len() as int / 2,
{
    if mutation_kind == 0 {
        // identity
        (nums, k)
    } else if mutation_kind == 1 {
        // set first element to 1 (min boundary)
        let mut d = nums;
        d.set(0, 1);
        (d, k)
    } else if mutation_kind == 2 {
        // set first element to 1000 (max boundary)
        let mut d = nums;
        d.set(0, 1000);
        (d, k)
    } else if mutation_kind == 3 {
        // set all elements to same value (no good elements except possibly edges)
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                2 <= d.len() <= 100,
                forall|j: int| 0 <= j < i ==> d[j] == 500,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 500);
            i += 1;
        }
        (d, k)
    } else if mutation_kind == 4 && nums.len() < 100 {
        // grow by one element (push 500)
        let mut d = nums;
        d.push(500);
        proof {
            assert(d.len() == nums.len() + 1);
            assert(2 <= d.len() <= 100);
            // k constraint: k <= nums.len()/2 <= (nums.len()+1)/2 = d.len()/2
            assert(k as int <= nums.len() as int / 2);
            assert(nums.len() as int / 2 <= d.len() as int / 2) by (nonlinear_arith)
                requires nums.len() as int + 1 == d.len() as int;
        }
        (d, k)
    } else if mutation_kind == 5 && nums.len() > 2 && (k as usize) <= (nums.len() - 1) / 2 {
        // shrink by one element (pop)
        let ghost old_len = nums.len();
        let mut d = nums;
        d.pop();
        proof {
            assert(d.len() as int == old_len as int - 1);
            assert(d.len() >= 2);
        }
        (d, k)
    } else if mutation_kind == 6 {
        // nudge first element up (if < 1000)
        let mut d = nums;
        if d[0] < 1000 {
            d.set(0, d[0] + 1);
        }
        (d, k)
    } else if mutation_kind == 7 {
        // nudge first element down (if > 1)
        let mut d = nums;
        if d[0] > 1 {
            d.set(0, d[0] - 1);
        }
        (d, k)
    } else if mutation_kind == 8 {
        // swap first two elements
        let mut d = nums;
        let tmp = d[0];
        d.set(0, d[1]);
        d.set(1, tmp);
        (d, k)
    } else if mutation_kind == 9 && k > 1 {
        // decrease k by 1
        (nums, k - 1)
    } else if mutation_kind == 10 && (k as usize + 1) <= nums.len() / 2 {
        // increase k by 1
        (nums, k + 1)
    } else if mutation_kind == 11 {
        // set k to 1 (minimum)
        (nums, 1)
    } else if mutation_kind == 12 {
        // set k to max (nums.len()/2)
        let max_k = (nums.len() / 2) as i32;
        proof {
            assert(nums.len() >= 2);
            assert(nums.len() as int / 2 >= 1) by (nonlinear_arith)
                requires nums.len() >= 2;
            assert(max_k as int == nums.len() as int / 2);
            assert(1 <= max_k);
        }
        (nums, max_k)
    } else if mutation_kind == 13 {
        // set last element to 1000
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 1000);
        (d, k)
    } else if mutation_kind == 14 {
        // set last element to 1
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 1);
        (d, k)
    } else {
        // fallback
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

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);

    use std::io::Write;
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);

    // Example inputs from description.md
    let examples: Vec<(Vec<i32>, i32)> = vec![
        (vec![1, 3, 2, 1, 5, 4], 2),
        (vec![2, 1], 1),
    ];

    let mut generated: usize = 0;

    // Emit examples first
    for (nums, k) in &examples {
        let result = Solution::sum_of_good_numbers(nums.clone(), *k);
        writeln!(out, "{}", json!({
            "input": {"nums": nums, "k": k},
            "output": result
        })).unwrap();
        generated += 1;
    }

    // Generate random test cases
    while generated < count {
        // Size class for array length
        let n: usize = match generated % 5 {
            0 => rng.gen_range_usize(2, 5),       // tiny
            1 => rng.gen_range_usize(2, 10),      // small
            2 => rng.gen_range_usize(11, 30),     // medium
            3 => rng.gen_range_usize(31, 70),     // large
            _ => rng.gen_range_usize(71, 100),    // max
        };

        // Build nums with values in [1, 1000]
        let mut nums: Vec<i32> = Vec::with_capacity(n);
        for _ in 0..n {
            let val = if rng.gen_range_usize(0, 4) == 0 {
                // boundary values ~20% of the time
                match rng.gen_range_usize(0, 3) {
                    0 => 1,
                    1 => 1000,
                    _ => 500,
                }
            } else {
                rng.gen_range_i64(1, 1000) as i32
            };
            nums.push(val);
        }

        // k in [1, n/2]
        let max_k = n / 2;
        let k: i32 = rng.gen_range_i64(1, max_k as i64) as i32;

        // Pick a mutation kind
        let mutation_kind: u8 = rng.gen_range_usize(0, 14) as u8;

        let (test_nums, test_k) = generate_test_case(nums, k, mutation_kind);
        let result = Solution::sum_of_good_numbers(test_nums.clone(), test_k);

        writeln!(out, "{}", json!({
            "input": {"nums": test_nums, "k": test_k},
            "output": result
        })).unwrap();

        generated += 1;
    }

    eprintln!("Generated {} test cases to {:?}", generated, out_path);
}
