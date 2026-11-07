use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32) -> (result: i32)
    requires
        2 <= n <= 100,
    ensures
        2 <= result <= 100,
{
    n
}

}

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
        assert!(lo <= hi);
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        lo + ((self.next_u64() % span) as i32)
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

fn pick_n(rng: &mut Rng, mode: usize) -> i32 {
    match mode {
        0 => 2,
        1 => 100,
        2 => 3,
        3 => 99,
        4 => 15,
        5 => rng.gen_range_i32(2, 10),
        6 => rng.gen_range_i32(50, 100),
        7 => rng.gen_range_i32(2, 100),
        8 => {
            let primes = [2i32, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97];
            primes[(rng.next_u64() as usize) % primes.len()]
        }
        9 => {
            let powers = [2i32, 4, 8, 16, 32, 64];
            powers[(rng.next_u64() as usize) % powers.len()]
        }
        _ => rng.gen_range_i32(2, 100),
    }
}

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
    let modes = 10usize;

    while count < target {
        let t: usize = if count < 10 { 1 }
                       else if count < 50 { rng.gen_range_usize(2, 10) }
                       else if count < 120 { rng.gen_range_usize(5, 30) }
                       else { rng.gen_range_usize(10, 100) };
        let mut ns: Vec<i32> = Vec::with_capacity(t);
        for sub in 0..t {
            let m = (count * 7 + sub) % modes;
            ns.push(pick_n(&mut rng, m));
        }
        let key = format!("{:?}", ns);
        if !seen.insert(key) { continue; }
        let answers: Vec<i32> = ns.iter().map(|&n| Solution::max_multiples_sum_x(n)).collect();
        let inp = build_input_multi(&ns);
        let outp = build_output_multi(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

