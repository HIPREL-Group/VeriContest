use vstd::prelude::*;

verus! {

pub fn generate_test_case(p: i64, m: i64) -> (result: (i64, i64))
    requires
        0 <= p <= 5000,
        0 <= m <= 5000,
    ensures
        result == (p, m),
{
    (p, m)
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

fn build_input_random(rng: &mut Rng, n: usize) -> (String, i64, i64) {
    let mut s = String::with_capacity(n);
    let mut p: i64 = 0;
    let mut m: i64 = 0;
    for _ in 0..n {
        if (rng.next_u64() & 1) == 1 {
            s.push('+'); p += 1;
        } else {
            s.push('-'); m += 1;
        }
    }
    let inp = format!("1\n{}\n{}\n", n, s);
    (inp, p, m)
}

fn main() {
    let target = 200usize;
    let mut rng = Rng::new(919191);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut seen: HashSet<String> = HashSet::new();
    let mut count = 0usize;
    let mut tries = 0;
    while count < target && tries < target * 50 {
        tries += 1;
        let n = 1 + (rng.next_u64() % 5000) as usize;
        let (inp, p, m) = build_input_random(&mut rng, n);
        if !seen.insert(inp.clone()) { continue; }
        let (p2, m2) = generate_test_case(p, m);
        let ans = Solution::min_penalty(p2, m2);
        let outp = format!("{}\n", ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}
