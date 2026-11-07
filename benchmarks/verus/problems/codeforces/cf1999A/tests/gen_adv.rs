use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_n: i32, mutation_kind: u8) -> (result: i32)
    requires
        10 <= seed_n <= 99,
    ensures
        10 <= result <= 99,
{
    if mutation_kind == 0 { 10i32 }
    else if mutation_kind == 1 { 99i32 }
    else if mutation_kind == 2 { 11i32 }
    else if mutation_kind == 3 { 90i32 }
    else { seed_n }
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

    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
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

fn build_input_multi(ns: &[i32]) -> String {
    let mut s = format!("{}\n", ns.len());
    for n in ns {
        s.push_str(&format!("{}\n", n));
    }
    s
}

fn build_output_multi(answers: &[i32]) -> String {
    let mut s = String::new();
    for a in answers {
        s.push_str(&format!("{}\n", a));
    }
    s
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

    while count < target && attempts < target * 10 {
        attempts += 1;
        let t: usize = if count < 20 { 1 }
                       else if count < 80 { rng.gen_range_usize(2, 10) }
                       else if count < 150 { rng.gen_range_usize(10, 50) }
                       else { rng.gen_range_usize(30, 90) };
        let mut ns: Vec<i32> = Vec::with_capacity(t);
        for _ in 0..t {
            let seed_n = rng.gen_range_i64(10, 99) as i32;
            let mk = (rng.next_u64() % 8) as u8;
            let n = generate_test_case(seed_n, mk);
            ns.push(n);
        }
        let key = format!("{:?}", ns);
        if !seen.insert(key) { continue; }
        let answers: Vec<i32> = ns.iter().map(|&n| Solution::two_digit_digit_sum(n)).collect();
        let inp = build_input_multi(&ns);
        let outp = build_output_multi(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}
