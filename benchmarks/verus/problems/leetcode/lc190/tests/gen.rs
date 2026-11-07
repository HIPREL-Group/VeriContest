use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        0 <= seed <= 2_147_483_646i32,
        seed % 2 == 0,
    ensures
        0 <= result <= 2_147_483_646i32,
        result % 2 == 0,
{
    if mutation_kind == 0 {
        seed
    } else if mutation_kind == 1 && seed <= 2_147_483_644 {
        seed + 2
    } else if mutation_kind == 2 && seed >= 2 {
        seed - 2
    } else if mutation_kind == 3 && seed <= 1_073_741_822 {
        seed * 2
    } else if mutation_kind == 4 {
        let h = seed / 2;
        let r = if h % 2 == 0 { h } else { h - 1 };
        r
    } else if mutation_kind == 5 {
        0i32
    } else if mutation_kind == 6 {
        2_147_483_646i32
    } else if mutation_kind == 7 {
        2i32
    } else {
        seed
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
        assert!(lo <= hi);
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
    let count_target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0;
    let num_mutations: u8 = 8;

    // Example inputs from description.md
    let examples: Vec<i32> = vec![43261596, 2147483644];
    for n in &examples {
        if count >= count_target { break; }
        if seen.insert(*n) {
            let result = Solution::reverse_bits(*n);
            writeln!(out, "{}", json!({"input": {"n": n}, "output": result})).unwrap();
            count += 1;
        }
    }

    // Seed pool: even values covering boundaries and interesting patterns
    let seeds: Vec<i32> = vec![
        0, 2, 4, 6, 8, 10, 100, 254, 256, 1000, 10000, 100000, 1000000,
        1 << 1, 1 << 2, 1 << 4, 1 << 8, 1 << 10, 1 << 15, 1 << 20, 1 << 29, 1 << 30,
        0b10101010, 0b01010100,
        0x7FFE, 0x7FFFFFFE,
        2_147_483_646, 2_147_483_644, 2_147_483_640,
        0x55555554, 0x2AAAAAA8,
        0x10000, 0x100, 0x10,
        42, 128, 512, 1024, 4096, 65536,
    ];

    // Seed pool x mutation_kind
    for &s in &seeds {
        for mk in 0..num_mutations {
            if count >= count_target { break; }
            let n = generate_test_case(s, mk);
            if seen.insert(n) {
                let result = Solution::reverse_bits(n);
                writeln!(out, "{}", json!({"input": {"n": n}, "output": result})).unwrap();
                count += 1;
            }
        }
    }

    // Fill remaining with random even seeds + random mutations
    while count < count_target {
        let s = rng.gen_range_i64(0, 1_073_741_323) as i32;
        let s = s * 2; // ensure even
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let n = generate_test_case(s, mk);
        if seen.insert(n) {
            let result = Solution::reverse_bits(n);
            writeln!(out, "{}", json!({"input": {"n": n}, "output": result})).unwrap();
            count += 1;
        }
    }
}
