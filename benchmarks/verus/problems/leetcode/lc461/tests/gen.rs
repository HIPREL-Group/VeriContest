use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_x: i32, seed_y: i32, mutation_kind: u8) -> (res: (i32, i32))
    requires
        0 <= seed_x <= i32::MAX,
        0 <= seed_y <= i32::MAX,
    ensures
        0 <= res.0 <= i32::MAX,
        0 <= res.1 <= i32::MAX,
{
    let x = if mutation_kind == 0 {
        seed_x
    } else if mutation_kind == 1 && seed_x < i32::MAX {
        seed_x + 1
    } else if mutation_kind == 2 && seed_x > 0 {
        seed_x - 1
    } else if mutation_kind == 3 && seed_x >= 0 && seed_x <= 1_073_741_823 {
        seed_x * 2
    } else if mutation_kind == 4 {
        seed_x / 2
    } else if mutation_kind == 5 {
        0
    } else if mutation_kind == 6 {
        i32::MAX
    } else {
        seed_x
    };

    let y = if mutation_kind == 7 && seed_y < i32::MAX {
        seed_y + 1
    } else if mutation_kind == 8 && seed_y > 0 {
        seed_y - 1
    } else if mutation_kind == 9 {
        seed_x
    } else if mutation_kind == 10 {
        if seed_y <= i32::MAX - seed_x { seed_x + seed_y } else { seed_y }
    } else {
        seed_y
    };

    (x, y)
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
    let mut rng = Rng::new(42);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0;
    let target = 100;
    let num_mutations: u8 = 11;

    let seeds: Vec<(i32, i32)> = vec![
        (0, 0), (0, i32::MAX), (i32::MAX, 0), (i32::MAX, i32::MAX),
        (1, 0), (0, 1), (1, 1), (1, 2), (1, 4),
        (2, 4), (4, 8), (8, 16), (16, 32),
        (1024, 2048), (1 << 15, 1 << 16), (1 << 20, 1 << 21), (1 << 29, 1 << 30),
        (42, 42), (255, 256), (1023, 1024), (100, 101),
        (0x7FFF_FFFF, 0), (0x5555_5555, 0x2AAA_AAAA),
        (0x7F7F_7F7F, 0x0F0F_0F0F),
    ];

    // Seed pool × mutation_kind
    for &(sx, sy) in &seeds {
        for mk in 0..num_mutations {
            if count >= target { break; }
            let (x, y) = generate_test_case(sx, sy, mk);
            if seen.insert((x as i64, y as i64)) {
                let result = Solution::hamming_distance(x, y);
                writeln!(out, "{}", json!({"input": {"x": x, "y": y}, "output": result})).unwrap();
                count += 1;
            }
        }
    }

    // Fill remaining with random seeds + random mutations
    while count < target {
        let sx = rng.gen_range_i64(0, i32::MAX as i64) as i32;
        let sy = rng.gen_range_i64(0, i32::MAX as i64) as i32;
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let (x, y) = generate_test_case(sx, sy, mk);
        if seen.insert((x as i64, y as i64)) {
            let result = Solution::hamming_distance(x, y);
            writeln!(out, "{}", json!({"input": {"x": x, "y": y}, "output": result})).unwrap();
            count += 1;
        }
    }
}
