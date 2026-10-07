use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_steps: i32, seed_arr_len: i32, mutation_kind: u8) -> (res: (i32, i32))
    requires
        1 <= seed_steps <= 500,
        1 <= seed_arr_len <= 1_000_000,
    ensures
        1 <= res.0 <= 500,
        1 <= res.1 <= 1_000_000,
{
    let steps = if mutation_kind == 0 {
        seed_steps
    } else if mutation_kind == 1 && seed_steps < 500 {
        seed_steps + 1
    } else if mutation_kind == 2 && seed_steps > 1 {
        seed_steps - 1
    } else if mutation_kind == 3 && seed_steps >= 2 && seed_steps <= 250 {
        seed_steps * 2
    } else if mutation_kind == 4 {
        if seed_steps / 2 >= 1 { seed_steps / 2 } else { 1 }
    } else if mutation_kind == 5 {
        1
    } else if mutation_kind == 6 {
        500
    } else {
        seed_steps
    };

    let arr_len = if mutation_kind == 7 && seed_arr_len < 1_000_000 {
        seed_arr_len + 1
    } else if mutation_kind == 8 && seed_arr_len > 1 {
        seed_arr_len - 1
    } else if mutation_kind == 9 {
        1
    } else if mutation_kind == 10 {
        1_000_000
    } else if mutation_kind == 11 {
        if seed_steps <= 1_000_000 { seed_steps as i32 } else { seed_arr_len }
    } else {
        seed_arr_len
    };

    (steps, arr_len)
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
    let num_mutations: u8 = 12;

    // Example inputs from description.md
    let examples: Vec<(i32, i32)> = vec![
        (3, 2),
        (2, 4),
        (4, 2),
    ];
    for (s, a) in &examples {
        if count >= goal { break; }
        if seen.insert((*s as i64, *a as i64)) {
            let output = Solution::num_ways(*s, *a);
            writeln!(out, "{}", json!({"input": {"steps": s, "arrLen": a}, "output": output})).unwrap();
            count += 1;
        }
    }

    // Seed pool: interesting values
    let seeds: Vec<(i32, i32)> = vec![
        (1, 1), (1, 2), (1, 1_000_000),
        (500, 1), (500, 2), (500, 1_000_000),
        (2, 1), (2, 2), (10, 10),
        (100, 100), (100, 1), (100, 1_000_000),
        (250, 500), (250, 1_000_000),
        (499, 500), (500, 500),
        (10, 1), (10, 5), (10, 100),
        (50, 25), (50, 1000),
        (200, 200), (300, 150),
    ];

    for &(ss, sa) in &seeds {
        for mk in 0..num_mutations {
            if count >= goal { break; }
            let (steps, arr_len) = generate_test_case(ss, sa, mk);
            if seen.insert((steps as i64, arr_len as i64)) {
                let output = Solution::num_ways(steps, arr_len);
                writeln!(out, "{}", json!({"input": {"steps": steps, "arrLen": arr_len}, "output": output})).unwrap();
                count += 1;
            }
        }
        if count >= goal { break; }
    }

    // Fill remaining with random seeds + random mutations
    while count < goal {
        let ss = rng.gen_range_i64(1, 500) as i32;
        let sa = rng.gen_range_i64(1, 1_000_000) as i32;
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let (steps, arr_len) = generate_test_case(ss, sa, mk);
        if seen.insert((steps as i64, arr_len as i64)) {
            let output = Solution::num_ways(steps, arr_len);
            writeln!(out, "{}", json!({"input": {"steps": steps, "arrLen": arr_len}, "output": output})).unwrap();
            count += 1;
        }
    }
}
