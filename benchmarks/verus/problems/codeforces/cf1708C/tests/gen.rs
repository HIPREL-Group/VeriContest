use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    a: Vec<i64>,
    q: i64,
    mutation_kind: u8,
) -> (result: (Vec<i64>, i64))
    requires
        1 <= a.len() <= 100_000,
        1 <= q <= 1_000_000_000,
        forall|j: int| 0 <= j < a.len() ==> 1 <= #[trigger] a[j] <= 1_000_000_000,
    ensures
        1 <= result.0.len() <= 100_000,
        1 <= result.1 <= 1_000_000_000,
        forall|j: int| 0 <= j < result.0.len() ==> 1 <= #[trigger] result.0[j] <= 1_000_000_000,
{
    if mutation_kind == 0 {
        // identity
        (a, q)
    } else if mutation_kind == 1 {
        // set first element to 1 (min boundary)
        let mut d = a;
        d.set(0, 1);
        (d, q)
    } else if mutation_kind == 2 {
        // set first element to 1_000_000_000 (max boundary)
        let mut d = a;
        d.set(0, 1_000_000_000);
        (d, q)
    } else if mutation_kind == 3 {
        // nudge first element up (if < max)
        let mut d = a;
        if d[0] < 1_000_000_000 {
            d.set(0, d[0] + 1);
        }
        (d, q)
    } else if mutation_kind == 4 {
        // nudge first element down (if > 1)
        let mut d = a;
        if d[0] > 1 {
            d.set(0, d[0] - 1);
        }
        (d, q)
    } else if mutation_kind == 5 {
        // set all elements to 1
        let mut d = a;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == a.len(),
                1 <= d.len() <= 100_000,
                forall|j: int| 0 <= j < i ==> d[j] == 1,
                forall|j: int| i <= j < d.len() ==> d[j] == a[j],
            decreases d.len() - i,
        {
            d.set(i, 1);
            i += 1;
        }
        (d, q)
    } else if mutation_kind == 6 {
        // set all elements to 1_000_000_000
        let mut d = a;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == a.len(),
                1 <= d.len() <= 100_000,
                forall|j: int| 0 <= j < i ==> d[j] == 1_000_000_000,
                forall|j: int| i <= j < d.len() ==> d[j] == a[j],
            decreases d.len() - i,
        {
            d.set(i, 1_000_000_000);
            i += 1;
        }
        (d, q)
    } else if mutation_kind == 7 && a.len() < 100_000 {
        // grow by one element
        let mut d = a;
        d.push(1);
        (d, q)
    } else if mutation_kind == 8 && a.len() > 1 {
        // shrink by one element
        let mut d = a;
        d.pop();
        (d, q)
    } else if mutation_kind == 9 && a.len() >= 2 {
        // swap first two elements
        let mut d = a;
        let tmp = d[0];
        d.set(0, d[1]);
        d.set(1, tmp);
        (d, q)
    } else if mutation_kind == 10 {
        // set q to 1 (min boundary)
        (a, 1)
    } else if mutation_kind == 11 {
        // set q to 1_000_000_000 (max boundary)
        (a, 1_000_000_000)
    } else if mutation_kind == 12 && q < 1_000_000_000 {
        // nudge q up
        (a, q + 1)
    } else if mutation_kind == 13 && q > 1 {
        // nudge q down
        (a, q - 1)
    } else {
        // fallback
        (a, q)
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

fn gen_valid_array(rng: &mut Rng, len: usize) -> Vec<i64> {
    let mut a = Vec::with_capacity(len);
    for _ in 0..len {
        a.push(rng.gen_range_i64(1, 1_000_000_000));
    }
    a
}

fn mutate(a: Vec<i64>, q: i64, mutation_kind: u8) -> (Vec<i64>, i64) {
    generate_test_case(a, q, mutation_kind)
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
    let examples: Vec<(Vec<i64>, i64)> = vec![
        (vec![1], 1),
        (vec![1, 2], 1),
        (vec![1, 2, 1], 1),
        (vec![1, 4, 3, 1], 2),
        (vec![5, 1, 2, 4, 3], 2),
    ];
    for (a, q) in examples {
        let result = Solution::optimal_tests(a.clone(), q);
        writeln!(out, "{}", json!({
            "input": {"a": a, "q": q},
            "output": result
        })).unwrap();
        generated += 1;
    }

    // Generate random test cases with diverse sizes and mutations
    let num_mutations: u8 = 14;

    while generated < count {
        // Size classes for array length
        let n: usize = match generated % 5 {
            0 => rng.gen_range_usize(1, 5),            // tiny
            1 => rng.gen_range_usize(1, 10),           // small
            2 => rng.gen_range_usize(11, 100),         // medium
            3 => rng.gen_range_usize(101, 1000),       // large
            _ => rng.gen_range_usize(1001, 10_000),    // big
        };

        let a = gen_valid_array(&mut rng, n);

        // q value with boundary mixing
        let q: i64 = if generated % 5 == 0 {
            *[1i64, 1_000_000_000, 2, 100, 999_999_999]
                .get(rng.gen_range_usize(0, 4))
                .unwrap()
        } else {
            rng.gen_range_i64(1, 1_000_000_000)
        };

        let mutation_kind = (rng.next_u64() % num_mutations as u64) as u8;
        let (mutated_a, mutated_q) = mutate(a, q, mutation_kind);

        let result = Solution::optimal_tests(mutated_a.clone(), mutated_q);
        writeln!(out, "{}", json!({
            "input": {"a": mutated_a, "q": mutated_q},
            "output": result
        })).unwrap();
        generated += 1;
    }

    eprintln!("Generated {} test cases to {:?}", generated, out_path);
}
