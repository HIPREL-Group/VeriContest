use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_h: u8, seed_m: u8, mutation_kind: u8) -> (result: (u8, u8))
    requires
        seed_h <= 23,
        seed_m <= 59,
    ensures
        result.0 <= 23,
        result.1 <= 59,
{
    if mutation_kind == 0 {
        (seed_h, seed_m)
    } else if mutation_kind == 1 {
        (0u8, seed_m)
    } else if mutation_kind == 2 {
        (12u8, seed_m)
    } else if mutation_kind == 3 {
        (23u8, seed_m)
    } else {
        (seed_h, seed_m)
    }
}

}

use std::io::Write;
use std::collections::HashSet;

struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0
    }
    fn gen_range_u8(&mut self, lo: u8, hi: u8) -> u8 {
        lo + ((self.next_u64() as u32) % ((hi - lo + 1) as u32)) as u8
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

fn fmt_json_str(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

struct Solution;
include!("../code.rs");

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(1950);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f_out = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f_out);
    let mut count = 0usize;
    let mut seen = HashSet::new();

    while count < target {
        let t = if count < 5 { 1usize } else { rng.gen_range_usize(1, 5) };
        let mut input = format!("{}\n", t);
        let mut output = String::new();
        for _ in 0..t {
            let h = rng.gen_range_u8(0, 23);
            let m = rng.gen_range_u8(0, 59);
            let mk = (rng.next_u64() % 5) as u8;
            let (hh, mm) = generate_test_case(h, m, mk);
            input.push_str(&format!("{:02}:{:02}\n", hh, mm));
            let converted = Solution::convert_time(hh, mm);
            output.push_str(&String::from_utf8(converted).unwrap());
            output.push('\n');
        }
        if !seen.insert(input.clone()) { continue; }
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&input), fmt_json_str(&output)).unwrap();
        count += 1;
    }
}
