use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_a: Vec<i64>, seed_b: Vec<i64>, m: usize) -> (result: (Vec<i64>, Vec<i64>, usize))
    requires
        1 <= seed_a.len() <= 50,
        seed_a.len() == seed_b.len(),
        1 <= m <= seed_a.len(),
        forall |i: int| 0 <= i < seed_a.len() ==> 1 <= #[trigger] seed_a[i] <= 1_000_000_000,
        forall |i: int| 0 <= i < seed_b.len() ==> 1 <= #[trigger] seed_b[i] <= 1_000_000_000,
    ensures
        1 <= result.2 <= result.0.len() <= 200_000,
        result.0.len() == result.1.len(),
        forall |i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 1_000_000_000,
        forall |i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i] <= 1_000_000_000,
{
    (seed_a, seed_b, m)
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

fn build_input(cases: &[(Vec<i64>, Vec<i64>, usize)]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (a, b, m) in cases {
        s.push_str(&format!("{} {}\n", a.len(), m));
        let parts_a: Vec<String> = a.iter().map(|x| x.to_string()).collect();
        s.push_str(&parts_a.join(" "));
        s.push('\n');
        let parts_b: Vec<String> = b.iter().map(|x| x.to_string()).collect();
        s.push_str(&parts_b.join(" "));
        s.push('\n');
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
    let mut rng = Rng::new(0x1945D);
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
        let mut cases: Vec<(Vec<i64>, Vec<i64>, usize)> = Vec::with_capacity(t);
        for _ in 0..t {
            let n = rng.gen_range_usize(1, 50);
            let m = rng.gen_range_usize(1, n);
            let seed_a: Vec<i64> = (0..n).map(|_| rng.gen_range_i64(1, 1_000_000_000)).collect();
            let seed_b: Vec<i64> = (0..n).map(|_| rng.gen_range_i64(1, 1_000_000_000)).collect();
            let (a, b, mm) = generate_test_case(seed_a, seed_b, m);
            cases.push((a, b, mm));
        }
        let answers: Vec<i64> = cases.iter().map(|(a, b, m)| Solution::min_coins(a.clone(), b.clone(), *m)).collect();
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}
