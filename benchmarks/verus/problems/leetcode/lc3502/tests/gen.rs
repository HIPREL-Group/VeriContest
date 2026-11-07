use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    // Construction parameters: raw element values and array length.
    elements: Vec<i32>,
    mutation_kind: u8,
) -> (result: Vec<i32>)
    requires
        1 <= elements.len() <= 100,
        forall |i: int| 0 <= i < elements.len() ==> 1 <= #[trigger] elements[i] <= 100,
    ensures
        1 <= result.len() <= 100,
        forall |i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 100,
{
    let mut cost: Vec<i32> = Vec::new();
    let n = elements.len();

    if mutation_kind == 0 {
        // Identity: copy elements as-is
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                n == elements.len(),
                cost.len() == k,
                forall |i: int| 0 <= i < k ==> 1 <= #[trigger] cost[i] <= 100,
                forall |i: int| 0 <= i < elements.len() ==> 1 <= #[trigger] elements[i] <= 100,
            decreases n - k,
        {
            cost.push(elements[k]);
            k += 1;
        }
        cost
    } else if mutation_kind == 1 && n >= 2 {
        // Shrink: drop last element
        let mut k: usize = 0;
        while k < n - 1
            invariant
                0 <= k <= n - 1,
                n == elements.len(),
                n >= 2,
                cost.len() == k,
                forall |i: int| 0 <= i < k ==> 1 <= #[trigger] cost[i] <= 100,
                forall |i: int| 0 <= i < elements.len() ==> 1 <= #[trigger] elements[i] <= 100,
            decreases n - k,
        {
            cost.push(elements[k]);
            k += 1;
        }
        cost
    } else if mutation_kind == 2 && n <= 99 {
        // Grow: append element[0] at end
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                n == elements.len(),
                n <= 99,
                cost.len() == k,
                forall |i: int| 0 <= i < k ==> 1 <= #[trigger] cost[i] <= 100,
                forall |i: int| 0 <= i < elements.len() ==> 1 <= #[trigger] elements[i] <= 100,
            decreases n - k,
        {
            cost.push(elements[k]);
            k += 1;
        }
        cost.push(elements[0]);
        cost
    } else if mutation_kind == 3 {
        // Set all elements to 1 (minimum boundary)
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                n == elements.len(),
                cost.len() == k,
                forall |i: int| 0 <= i < k ==> #[trigger] cost[i] == 1,
            decreases n - k,
        {
            cost.push(1i32);
            k += 1;
        }
        cost
    } else if mutation_kind == 4 {
        // Set all elements to 100 (maximum boundary)
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                n == elements.len(),
                cost.len() == k,
                forall |i: int| 0 <= i < k ==> #[trigger] cost[i] == 100,
            decreases n - k,
        {
            cost.push(100i32);
            k += 1;
        }
        cost
    } else if mutation_kind == 5 && n >= 2 {
        // Swap first two elements
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                n == elements.len(),
                n >= 2,
                cost.len() == k,
                forall |i: int| 0 <= i < k ==> 1 <= #[trigger] cost[i] <= 100,
                forall |i: int| 0 <= i < elements.len() ==> 1 <= #[trigger] elements[i] <= 100,
            decreases n - k,
        {
            if k == 0 {
                cost.push(elements[1]);
            } else if k == 1 {
                cost.push(elements[0]);
            } else {
                cost.push(elements[k]);
            }
            k += 1;
        }
        cost
    } else if mutation_kind == 6 {
        // Nudge first element: clamp(elem[0]+1, 1, 100)
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                n == elements.len(),
                cost.len() == k,
                forall |i: int| 0 <= i < k ==> 1 <= #[trigger] cost[i] <= 100,
                forall |i: int| 0 <= i < elements.len() ==> 1 <= #[trigger] elements[i] <= 100,
            decreases n - k,
        {
            if k == 0 {
                let v = if elements[0] < 100 { (elements[0] + 1) as i32 } else { 100i32 };
                cost.push(v);
            } else {
                cost.push(elements[k]);
            }
            k += 1;
        }
        cost
    } else if mutation_kind == 7 {
        // Nudge first element down: clamp(elem[0]-1, 1, 100)
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                n == elements.len(),
                cost.len() == k,
                forall |i: int| 0 <= i < k ==> 1 <= #[trigger] cost[i] <= 100,
                forall |i: int| 0 <= i < elements.len() ==> 1 <= #[trigger] elements[i] <= 100,
            decreases n - k,
        {
            if k == 0 {
                let v = if elements[0] > 1 { (elements[0] - 1) as i32 } else { 1i32 };
                cost.push(v);
            } else {
                cost.push(elements[k]);
            }
            k += 1;
        }
        cost
    } else {
        // Fallback: identity
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                n == elements.len(),
                cost.len() == k,
                forall |i: int| 0 <= i < k ==> 1 <= #[trigger] cost[i] <= 100,
                forall |i: int| 0 <= i < elements.len() ==> 1 <= #[trigger] elements[i] <= 100,
            decreases n - k,
        {
            cost.push(elements[k]);
            k += 1;
        }
        cost
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
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);

    let mut generated = 0usize;

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![5, 3, 4, 1, 3, 2],
        vec![1, 2, 4, 6, 7],
    ];
    for ex in &examples {
        let cost = ex.clone();
        let answer = Solution::min_costs(cost.clone());
        writeln!(out, "{}", json!({"input": {"cost": cost}, "output": answer})).unwrap();
        generated += 1;
    }

    // Generate remaining test cases with diverse sizes and mutations
    while generated < count {
        // Size classes
        let n: usize = match generated % 5 {
            0 => rng.gen_range_usize(1, 3),       // tiny
            1 => rng.gen_range_usize(1, 10),      // small
            2 => rng.gen_range_usize(11, 30),     // medium
            3 => rng.gen_range_usize(31, 70),     // large
            _ => rng.gen_range_usize(71, 100),    // max
        };

        // Build elements with diverse value strategies
        let mut elements: Vec<i32> = Vec::with_capacity(n);
        let val_strategy = generated % 4;
        for _j in 0..n {
            let v: i32 = match val_strategy {
                0 => rng.gen_range_i64(1, 100) as i32,           // uniform random
                1 => rng.gen_range_i64(1, 10) as i32,            // small values
                2 => rng.gen_range_i64(90, 100) as i32,          // large values
                _ => {
                    // boundary mix
                    let pick = rng.gen_range_usize(0, 4);
                    match pick {
                        0 => 1,
                        1 => 100,
                        2 => 50,
                        3 => rng.gen_range_i64(1, 100) as i32,
                        _ => rng.gen_range_i64(1, 100) as i32,
                    }
                }
            };
            elements.push(v);
        }

        let mutation_kind = (rng.gen_u8()) % 9;
        let cost = generate_test_case(elements, mutation_kind);
        let answer = Solution::min_costs(cost.clone());
        writeln!(out, "{}", json!({"input": {"cost": cost}, "output": answer})).unwrap();
        generated += 1;
    }

    eprintln!("Generated {} test cases to {:?}", generated, out_path);
}
