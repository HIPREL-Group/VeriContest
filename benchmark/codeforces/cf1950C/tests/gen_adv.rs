use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_h: u8, seed_m: u8) -> (result: (u8, u8))
    requires
        seed_h <= 23,
        seed_m <= 59,
    ensures
        result.0 <= 23,
        result.1 <= 59,
{
    (seed_h, seed_m)
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

fn build_input(cases: &[(u8, u8)]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (h, m) in cases {
        s.push_str(&format!("{:02}:{:02}\n", h, m));
    }
    s
}

fn build_output(answers: &[Vec<u8>]) -> String {
    let mut s = String::new();
    for answer in answers {
        s.push_str(&String::from_utf8(answer.clone()).unwrap());
        s.push('\n');
    }
    s
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(0x1950C);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut count = 0usize;
    let mut seen = HashSet::new();

    while count < target {
        let t: usize = if count < 20 { 1 }
                       else if count < 80 { rng.gen_range_usize(2, 6) }
                       else if count < 150 { rng.gen_range_usize(3, 15) }
                       else { rng.gen_range_usize(5, 30) };
        let mut cases: Vec<(u8, u8)> = Vec::with_capacity(t);
        for _ in 0..t {
            let h = rng.gen_range_u8(0, 23);
            let m = rng.gen_range_u8(0, 59);
            let (hh, mm) = generate_test_case(h, m);
            cases.push((hh, mm));
        }
        let answers: Vec<Vec<u8>> = cases.iter()
            .map(|(h, m)| Solution::convert_time(*h, *m))
            .collect();
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}
