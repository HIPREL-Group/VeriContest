use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        -2_147_483_648i32 <= seed <= 2_147_483_647i32,
    ensures
        -2_147_483_648i32 <= result <= 2_147_483_647i32,
{
    if mutation_kind == 0 {
        seed
    } else if mutation_kind == 1 && seed < i32::MAX {
        seed + 1
    } else if mutation_kind == 2 && seed > i32::MIN {
        seed - 1
    } else if mutation_kind == 3 && seed > i32::MIN {
        -seed
    } else if mutation_kind == 4 {
        if seed >= -1_073_741_824 && seed <= 1_073_741_823 {
            seed * 2
        } else {
            seed
        }
    } else if mutation_kind == 5 {
        seed / 2
    } else if mutation_kind == 6 {
        0
    } else if mutation_kind == 7 {
        i32::MIN
    } else if mutation_kind == 8 {
        i32::MAX
    } else if mutation_kind == 9 {
        if seed > i32::MIN {
            if seed >= 0 { seed } else { -seed }
        } else {
            seed
        }
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
    let mut rng = Rng::new(42);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;
    let goal = 100usize;

    // Seed pool: powers of 4 and interesting values
    let mut seeds: Vec<i32> = vec![
        0, 1, -1, 2, -2, 3, -3, 4, -4,
        i32::MAX, i32::MIN, i32::MAX - 1, i32::MIN + 1,
        100, -100, 1000, -1000,
    ];
    // Powers of 4: 1, 4, 16, 64, ..., 4^15 = 1073741824
    let mut p: i64 = 1;
    while p <= i32::MAX as i64 {
        seeds.push(p as i32);
        if p > 1 {
            seeds.push((p - 1) as i32);
            seeds.push((p + 1).min(i32::MAX as i64) as i32);
        }
        p *= 4;
    }
    // Powers of 2 that are NOT powers of 4
    for &v in &[2i32, 8, 32, 128, 512, 2048, 8192, 32768, 131072, 524288] {
        seeds.push(v);
    }
    // Negative values
    for &v in &[-4i32, -16, -64, -256, -1024, -4096, -16384, -65536] {
        seeds.push(v);
    }

    for &seed in &seeds {
        for mk in 0..=10u8 {
            if count >= goal { break; }
            let n = generate_test_case(seed, mk);
            if seen.insert(n) {
                let output = Solution::is_power_of_four(n);
                writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
                count += 1;
            }
        }
        if count >= goal { break; }
    }

    while count < goal {
        let seed = rng.gen_range_i64(i32::MIN as i64, i32::MAX as i64) as i32;
        let mk = rng.gen_u8() % 11;
        let n = generate_test_case(seed, mk);
        if seen.insert(n) {
            let output = Solution::is_power_of_four(n);
            writeln!(out, "{}", json!({"input": {"n": n}, "output": output})).unwrap();
            count += 1;
        }
    }
}
