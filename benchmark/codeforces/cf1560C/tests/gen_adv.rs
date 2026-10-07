use vstd::prelude::*;

verus! {

pub fn generate_test_case(k: i64) -> (res: i64)
    requires
        1 <= k <= 1_000_000_000,
    ensures
        1 <= res <= 1_000_000_000,
{
    k
}

}

use std::io::Write;
use std::collections::HashSet;

struct Rng { state: u64 }
impl Rng {
    fn new(seed: u64) -> Self { Self { state: seed } }
    fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.state
    }
    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let span = (hi as i128 - lo as i128 + 1) as u128;
        let v = (self.next_u64() as u128) % span;
        lo + v as i64
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
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

fn pick_k(rng: &mut Rng, mode: usize) -> i64 {
    let specials: [i64; 31] = [
        1, 2, 3, 4, 5, 6, 7, 8, 9, 10,
        11, 14, 16, 25, 100, 99, 101,
        999_999_999, 1_000_000_000,
        999_950_884, 999_950_885, 999_950_886,
        2, 3, 5, 7,
        65_536, 131_072,
        262_144, 524_288, 268_435_456,
    ];
    match mode {
        0 => { let idx = (rng.next_u64() as usize) % specials.len(); specials[idx] }
        1 => rng.gen_range_i64(1, 100),
        2 => rng.gen_range_i64(1, 10_000),
        3 => rng.gen_range_i64(1, 1_000_000),
        4 => rng.gen_range_i64(900_000_000, 1_000_000_000),
        5 => { let s = rng.gen_range_i64(1, 31622); s * s }
        6 => {
            let s = rng.gen_range_i64(1, 31622);
            let v = (s - 1) * (s - 1) + 1;
            if v < 1 { 1 } else if v > 1_000_000_000 { 1_000_000_000 } else { v }
        }
        7 => {
            let s = rng.gen_range_i64(2, 31622);
            let v = s * s - 1;
            if v < 1 { 1 } else if v > 1_000_000_000 { 1_000_000_000 } else { v }
        }
        8 => {
            let s = rng.gen_range_i64(1, 31622);
            let v = (s - 1) * (s - 1) + s;
            if v < 1 { 1 } else if v > 1_000_000_000 { 1_000_000_000 } else { v }
        }
        9 => rng.gen_range_i64(1, 1_000_000_000),
        _ => rng.gen_range_i64(1, 1_000_000_000),
    }
}

fn build_input(ks: &[i64]) -> String {
    let mut s = format!("{}\n", ks.len());
    for &k in ks { s.push_str(&format!("{}\n", k)); }
    s
}

fn build_output(answers: &[(i64, i64)]) -> String {
    let mut s = String::new();
    for &(r, c) in answers { s.push_str(&format!("{} {}\n", r, c)); }
    s
}

fn main() {
    let mut rng = Rng::new(1);
    let modes = 10usize;
    let total = 200usize;

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut seen: HashSet<String> = HashSet::new();
    let mut count = 0usize;
    let mut idx = 0usize;
    while count < total {
        let t: usize = if count < 10 { 1 } else { rng.gen_range_usize(1, 50) };
        let mut ks: Vec<i64> = Vec::new();
        for _ in 0..t {
            let mode = idx % modes;
            idx += 1;
            let k = pick_k(&mut rng, mode);
            let k_safe = if k < 1 { 1 } else if k > 1_000_000_000 { 1_000_000_000 } else { k };
            ks.push(k_safe);
        }
        let inp = build_input(&ks);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<(i64, i64)> = ks.iter().map(|&k| Solution::infinity_table_cell(k)).collect();
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

