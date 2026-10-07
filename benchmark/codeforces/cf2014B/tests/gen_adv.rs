use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_n: i64, seed_k: i64, mutation_kind: u8) -> (result: (i64, i64))
    requires
        1 <= seed_n <= 1_000_000_000,
        1 <= seed_k <= seed_n,
    ensures
        1 <= result.0 <= 1_000_000_000,
        1 <= result.1 <= result.0,
{
    if mutation_kind == 0 { (1i64, 1i64) }
    else if mutation_kind == 1 { (1_000_000_000i64, 1i64) }
    else if mutation_kind == 2 { (1_000_000_000i64, 1_000_000_000i64) }
    else if mutation_kind == 3 { (seed_n, seed_n) }
    else if mutation_kind == 4 { (seed_n, 1i64) }
    else { (seed_n, seed_k) }
}

} // verus!

use std::io::Write;

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

fn build_input(cases: &[(i64, i64)]) -> String {
    let mut s = format!("{}\n", cases.len());
    for &(n, k) in cases {
        s.push_str(&format!("{} {}\n", n, k));
    }
    s
}

fn build_output(answers: &[bool]) -> String {
    let mut s = String::new();
    for &a in answers {
        s.push_str(if a { "YES\n" } else { "NO\n" });
    }
    s
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(1);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut count = 0usize;

    while count < target {
        let t: usize = if count < 20 { 1 }
                       else if count < 80 { rng.gen_range_usize(2, 10) }
                       else if count < 150 { rng.gen_range_usize(5, 30) }
                       else { rng.gen_range_usize(10, 100) };
        let mut cases: Vec<(i64, i64)> = Vec::with_capacity(t);
        for sub in 0..t {
            // generate seed values that satisfy precondition (1 <= seed_k <= seed_n)
            let seed_n = rng.gen_range_i64(1, 1_000_000_000);
            let seed_k = rng.gen_range_i64(1, seed_n);
            let mk = ((count + sub) % 7) as u8;
            let (n, k) = generate_test_case(seed_n, seed_k, mk);
            cases.push((n, k));
        }
        let answers: Vec<bool> = cases.iter().map(|&(n, k)| Solution::major_oak_leaves_even(n, k)).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}
