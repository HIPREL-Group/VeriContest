use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_k: u64) -> (res: u64)
    requires
        1 <= seed_k <= 1_000_000_000_000_000_000u64,
    ensures
        1 <= res <= 1_000_000_000_000_000_000u64,
{
    seed_k
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

    fn gen_range_u64(&mut self, lo: u64, hi: u64) -> u64 {
        let range = (hi - lo + 1) as u128;
        lo + (self.next_u64() as u128 % range) as u64
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

fn build_input(ks: &[u64]) -> String {
    let mut s = format!("{}\n", ks.len());
    for k in ks {
        s.push_str(&format!("{}\n", k));
    }
    s
}

fn build_output(answers: &[u64]) -> String {
    let mut s = String::new();
    for ans in answers {
        s.push_str(&format!("{}\n", ans));
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
                       else if count < 80 { rng.gen_range_usize(2, 6) }
                       else if count < 150 { rng.gen_range_usize(3, 12) }
                       else { rng.gen_range_usize(5, 25) };
        let mut ks: Vec<u64> = Vec::with_capacity(t);
        for sub in 0..t {
            let mode = (count + sub) % 7;
            // Note: the brute solver uses ub = k + 2_000_000_000 + 1000, very slow for big k
            // we limit k aggressively here so it stays fast enough
            let seed_k = match mode {
                0 => 1u64 + (count as u64) * 7 + (sub as u64),
                1 => rng.gen_range_u64(1, 100),
                2 => rng.gen_range_u64(1, 10_000),
                3 => rng.gen_range_u64(1, 100_000),
                4 => rng.gen_range_u64(1, 1_000_000),
                5 => rng.gen_range_u64(100, 10_000),
                _ => rng.gen_range_u64(1, 1_000_000),
            };
            // pass through verified function
            let k = generate_test_case(seed_k);
            ks.push(k);
        }
        let inp = build_input(&ks);
        let answers: Vec<u64> = ks.iter().map(|&k| Solution::min_bulbs_n(k)).collect();
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}
