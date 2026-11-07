use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_a: Vec<i64>, seed_s: Vec<u8>) -> (result: (Vec<i64>, Vec<u8>))
    requires
        2 <= seed_a.len() <= 30,
        seed_a.len() == seed_s.len(),
        forall |i: int| 0 <= i < seed_a.len() ==> 1 <= #[trigger] seed_a[i] <= 100_000,
        forall |i: int| 0 <= i < seed_s.len() ==> #[trigger] seed_s[i] == 1u8 || seed_s[i] == 2u8,
    ensures
        2 <= result.0.len() <= 200_000,
        result.0.len() == result.1.len(),
        forall |i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 100_000,
        forall |i: int| 0 <= i < result.1.len() ==> #[trigger] result.1[i] == 1u8 || result.1[i] == 2u8,
{
    (seed_a, seed_s)
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

fn vec_to_str(v: &Vec<u8>) -> String {
    let mut s = String::with_capacity(v.len());
    for x in v {
        s.push(if *x == 1 { 'L' } else { 'R' });
    }
    s
}

fn build_input(cases: &[(Vec<i64>, Vec<u8>)]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (a, st) in cases {
        s.push_str(&format!("{}\n", a.len()));
        let parts: Vec<String> = a.iter().map(|v| v.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
        s.push_str(&format!("{}\n", vec_to_str(st)));
    }
    s
}

fn build_output(answers: &[i64]) -> String {
    let mut s = String::new();
    for ans in answers {
        s.push_str(&format!("{}\n", ans));
    }
    s
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(0x2000D);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut count = 0usize;
    let mut seen = HashSet::new();

    while count < target {
        let t: usize = if count < 20 { 1 }
                       else if count < 80 { rng.gen_range_usize(2, 6) }
                       else { rng.gen_range_usize(2, 10) };
        let mut cases: Vec<(Vec<i64>, Vec<u8>)> = Vec::with_capacity(t);
        for _ in 0..t {
            let n = rng.gen_range_usize(2, 30);
            let seed_a: Vec<i64> = (0..n).map(|_| rng.gen_range_i64(1, 100_000)).collect();
            let seed_s: Vec<u8> = (0..n).map(|_| if rng.next_u64() & 1 == 0 { 1u8 } else { 2u8 }).collect();
            let (a, s) = generate_test_case(seed_a, seed_s);
            cases.push((a, s));
        }
        let answers: Vec<i64> = cases.iter().map(|(a, s)| Solution::max_score(a.clone(), s.clone())).collect();
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}
