use vstd::prelude::*;

verus! {

pub fn generate_test_case(base_vals: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        3 <= base_vals.len() <= 50,
        forall|i: int| 0 <= i < base_vals.len() ==> 1 <= #[trigger] base_vals[i] <= 50,
    ensures
        3 <= result.len() <= 50,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 50,
{
    if mutation_kind == 0 {
        // identity
        base_vals
    } else if mutation_kind == 1 {
        // set last element to 1 (min boundary)
        let mut v = base_vals;
        let last = v.len() - 1;
        v.set(last, 1);
        v
    } else if mutation_kind == 2 {
        // set last element to 50 (max boundary)
        let mut v = base_vals;
        let last = v.len() - 1;
        v.set(last, 50);
        v
    } else if mutation_kind == 3 {
        // set all elements to 1
        let mut v = base_vals;
        let mut i: usize = 0;
        while i < v.len()
            invariant
                0 <= i <= v.len(),
                v.len() == base_vals.len(),
                3 <= v.len() <= 50,
                forall|j: int| 0 <= j < i ==> v[j] == 1i32,
                forall|j: int| i <= j < v.len() ==> v[j] == base_vals[j],
            decreases v.len() - i,
        {
            v.set(i, 1);
            i += 1;
        }
        v
    } else if mutation_kind == 4 {
        // set all elements to 50
        let mut v = base_vals;
        let mut i: usize = 0;
        while i < v.len()
            invariant
                0 <= i <= v.len(),
                v.len() == base_vals.len(),
                3 <= v.len() <= 50,
                forall|j: int| 0 <= j < i ==> v[j] == 50i32,
                forall|j: int| i <= j < v.len() ==> v[j] == base_vals[j],
            decreases v.len() - i,
        {
            v.set(i, 50);
            i += 1;
        }
        v
    } else if mutation_kind == 5 && base_vals.len() < 50 {
        // grow by one element (push 1)
        let mut v = base_vals;
        v.push(1);
        v
    } else if mutation_kind == 6 && base_vals.len() > 3 {
        // shrink by one element (pop)
        let mut v = base_vals;
        v.pop();
        v
    } else if mutation_kind == 7 {
        // nudge second element: if < 50, increment by 1
        let mut v = base_vals;
        if v[1] < 50 {
            v.set(1, v[1] + 1);
        }
        v
    } else if mutation_kind == 8 {
        // nudge second element down: if > 1, decrement by 1
        let mut v = base_vals;
        if v[1] > 1 {
            v.set(1, v[1] - 1);
        }
        v
    } else if mutation_kind == 9 && base_vals.len() >= 4 {
        // swap second and third elements
        let mut v = base_vals;
        let tmp = v[1];
        v.set(1, v[2]);
        v.set(2, tmp);
        v
    } else {
        // fallback: identity
        base_vals
    }
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

struct Solution;
include!("../code.rs");

fn mutate(nums: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(nums, mutation_kind)
}

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(1, 50) as i32);
    }
    nums
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
    let mut generated: usize = 0;

    // Example test cases from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![1, 2, 3, 12],
        vec![5, 4, 3],
        vec![10, 3, 1, 1],
    ];
    for nums in &examples {
        let result = Solution::minimum_cost(nums.clone());
        writeln!(out, "{}", json!({
            "input": {"nums": nums},
            "output": result
        })).unwrap();
        generated += 1;
    }

    // Systematic: various sizes × mutation kinds
    let mutation_count: u8 = 10;
    while generated < count {
        let n: usize = match generated % 5 {
            0 => 3,                                          // minimum size
            1 => rng.gen_range_usize(3, 5),                  // tiny
            2 => rng.gen_range_usize(6, 15),                 // small
            3 => rng.gen_range_usize(16, 35),                // medium
            _ => rng.gen_range_usize(36, 50),                // large / max
        };

        let base = random_nums(&mut rng, n);
        let mk = (rng.next_u64() % mutation_count as u64) as u8;
        let nums = mutate(base, mk);

        let result = Solution::minimum_cost(nums.clone());
        writeln!(out, "{}", json!({
            "input": {"nums": nums},
            "output": result
        })).unwrap();

        generated += 1;
    }
}
