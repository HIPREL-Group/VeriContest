use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_n: u64, seed_m: u64, seed_a: u64, mutation_kind: u8) -> (result: (u64, u64, u64))
    requires
        1 <= seed_n <= 1_000_000_000,
        1 <= seed_m <= 1_000_000_000,
        1 <= seed_a <= 1_000_000_000,
    ensures
        1 <= result.0 <= 1_000_000_000,
        1 <= result.1 <= 1_000_000_000,
        1 <= result.2 <= 1_000_000_000,
{
    if mutation_kind == 0 { (1u64, 1u64, 1u64) }
    else if mutation_kind == 1 { (1_000_000_000u64, 1_000_000_000u64, 1u64) }
    else if mutation_kind == 2 { (1_000_000_000u64, 1_000_000_000u64, 1_000_000_000u64) }
    else if mutation_kind == 3 { (1u64, 1u64, 1_000_000_000u64) }
    else if mutation_kind == 4 { (seed_n, seed_n, seed_n) }
    else { (seed_n, seed_m, seed_a) }
}

} // verus!

use std::io::Write;
use std::collections::HashSet;

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }

    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0
    }

    fn gen_range_u64(&mut self, lo: u64, hi: u64) -> u64 {
        let range = (hi - lo + 1) as u128;
        lo + (self.next_u64() as u128 % range) as u64
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

fn build_input(n: u64, m: u64, a: u64) -> String {
    format!("{} {} {}\n", n, m, a)
}

fn build_output(ans: u64) -> String {
    format!("{}\n", ans)
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(1);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut count = 0usize;
    let mut attempts = 0usize;

    while count < target && attempts < target * 20 {
        attempts += 1;
        let seed_n = rng.gen_range_u64(1, 1_000_000_000);
        let seed_m = rng.gen_range_u64(1, 1_000_000_000);
        let seed_a = rng.gen_range_u64(1, 1_000_000_000);
        let mk = (rng.next_u64() % 11) as u8;
        let (n, m, a) = generate_test_case(seed_n, seed_m, seed_a, mk);
        if !seen.insert((n, m, a)) { continue; }
        let inp = build_input(n, m, a);
        let outp = build_output(Solution::min_flagstones(n, m, a));
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}
