use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_l: i32, seed_r: i32, seed_ll: i32, seed_rr: i32, mutation_kind: u8) -> (result: (i32, i32, i32, i32))
    requires
        1 <= seed_l < seed_r <= 100,
        1 <= seed_ll < seed_rr <= 100,
    ensures
        1 <= result.0 < result.1 <= 100,
        1 <= result.2 < result.3 <= 100,
{
    if mutation_kind == 0 { (1i32, 100i32, 1i32, 100i32) }
    else if mutation_kind == 1 { (1i32, 2i32, 99i32, 100i32) }
    else if mutation_kind == 2 { (seed_l, seed_r, seed_l, seed_r) }
    else if mutation_kind == 3 { (1i32, 2i32, 1i32, 2i32) }
    else if mutation_kind == 4 { (99i32, 100i32, 99i32, 100i32) }
    else { (seed_l, seed_r, seed_ll, seed_rr) }
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

fn build_input(cases: &[(i32, i32, i32, i32)]) -> String {
    let mut s = format!("{}\n", cases.len());
    for &(l, r, ll, rr) in cases {
        s.push_str(&format!("{} {}\n{} {}\n", l, r, ll, rr));
    }
    s
}

fn build_output(answers: &[i32]) -> String {
    let mut s = String::new();
    for a in answers {
        s.push_str(&format!("{}\n", a));
    }
    s
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(1);
    let mut seen: HashSet<String> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut count = 0usize;
    let mut attempts = 0usize;

    while count < target && attempts < target * 10 {
        attempts += 1;
        let t: usize = if count < 20 { 1 }
                       else if count < 80 { rng.gen_range_usize(2, 6) }
                       else if count < 150 { rng.gen_range_usize(3, 15) }
                       else { rng.gen_range_usize(5, 30) };
        let mut cases: Vec<(i32, i32, i32, i32)> = Vec::with_capacity(t);
        for _ in 0..t {
            // Generate seed values that satisfy the precondition
            let seed_l = rng.gen_range_i64(1, 99) as i32;
            let seed_r = rng.gen_range_i64(seed_l as i64 + 1, 100) as i32;
            let seed_ll = rng.gen_range_i64(1, 99) as i32;
            let seed_rr = rng.gen_range_i64(seed_ll as i64 + 1, 100) as i32;
            let mk = (rng.next_u64() % 8) as u8;
            let (l, r, ll, rr) = generate_test_case(seed_l, seed_r, seed_ll, seed_rr, mk);
            cases.push((l, r, ll, rr));
        }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<i32> = cases.iter().map(|&(l, r, ll, rr)| Solution::min_doors_to_lock(l, r, ll, rr)).collect();
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}
