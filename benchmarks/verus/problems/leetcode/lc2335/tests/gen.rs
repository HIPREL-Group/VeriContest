use vstd::prelude::*;

verus! {

pub fn generate_test_case(a: i32, b: i32, c: i32, mutation_kind: u8) -> (amount: Vec<i32>)
    requires
        0 <= a <= 100,
        0 <= b <= 100,
        0 <= c <= 100,
    ensures
        amount.len() == 3,
        0 <= amount[0] <= 100,
        0 <= amount[1] <= 100,
        0 <= amount[2] <= 100,
{
    let mut v: Vec<i32> = Vec::new();
    if mutation_kind == 0 {
        // identity
        v.push(a);
        v.push(b);
        v.push(c);
        v
    } else if mutation_kind == 1 {
        // set first to 0
        v.push(0);
        v.push(b);
        v.push(c);
        v
    } else if mutation_kind == 2 {
        // set all to 0
        v.push(0);
        v.push(0);
        v.push(0);
        v
    } else if mutation_kind == 3 {
        // set all to 100
        v.push(100);
        v.push(100);
        v.push(100);
        v
    } else if mutation_kind == 4 {
        // nudge a up
        if a < 100 {
            v.push(a + 1);
        } else {
            v.push(a);
        }
        v.push(b);
        v.push(c);
        v
    } else if mutation_kind == 5 {
        // nudge a down
        if a > 0 {
            v.push(a - 1);
        } else {
            v.push(a);
        }
        v.push(b);
        v.push(c);
        v
    } else if mutation_kind == 6 {
        // set b = a (duplicate values)
        v.push(a);
        v.push(a);
        v.push(c);
        v
    } else if mutation_kind == 7 {
        // set all equal to a
        v.push(a);
        v.push(a);
        v.push(a);
        v
    } else if mutation_kind == 8 {
        // swap a and b
        v.push(b);
        v.push(a);
        v.push(c);
        v
    } else if mutation_kind == 9 {
        // halve a
        v.push(a / 2);
        v.push(b);
        v.push(c);
        v
    } else {
        // fallback: identity
        v.push(a);
        v.push(b);
        v.push(c);
        v
    }
}

} // verus!

extern crate serde_json;
use serde_json::json;

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
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    // Example inputs from the problem description
    let examples: Vec<(i32, i32, i32)> = vec![
        (1, 4, 2),
        (5, 4, 4),
        (5, 0, 0),
    ];

    for (a, b, c) in &examples {
        if count >= goal { break; }
        let amount = vec![*a, *b, *c];
        let key = (amount[0], amount[1], amount[2]);
        if seen.insert(key) {
            let output = Solution::fill_cups(amount.clone());
            writeln!(out, "{}", json!({"input": {"amount": amount}, "output": output})).unwrap();
            count += 1;
        }
    }

    // Seed pool: boundary and interesting values
    let interesting: Vec<i32> = vec![0, 1, 2, 50, 99, 100];

    // Iterate interesting triples × mutation kinds
    for &a in &interesting {
        for &b in &interesting {
            for &c in &interesting {
                for mk in 0..=10u8 {
                    if count >= goal { break; }
                    let amount = generate_test_case(a, b, c, mk);
                    let key = (amount[0], amount[1], amount[2]);
                    if seen.insert(key) {
                        let output = Solution::fill_cups(amount.clone());
                        writeln!(out, "{}", json!({"input": {"amount": amount}, "output": output})).unwrap();
                        count += 1;
                    }
                }
                if count >= goal { break; }
            }
            if count >= goal { break; }
        }
        if count >= goal { break; }
    }

    // Fill remaining with random inputs + random mutations
    while count < goal {
        let a = rng.gen_range_i64(0, 100) as i32;
        let b = rng.gen_range_i64(0, 100) as i32;
        let c = rng.gen_range_i64(0, 100) as i32;
        let mk = rng.gen_u8() % 11;
        let amount = generate_test_case(a, b, c, mk);
        let key = (amount[0], amount[1], amount[2]);
        if seen.insert(key) {
            let output = Solution::fill_cups(amount.clone());
            writeln!(out, "{}", json!({"input": {"amount": amount}, "output": output})).unwrap();
            count += 1;
        }
    }
}
