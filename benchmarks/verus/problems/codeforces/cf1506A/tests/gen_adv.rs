use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: u64, m: u64, x: u64) -> (result: (u64, u64, u64))
    requires
        1 <= n <= 1_000_000,
        1 <= m <= 1_000_000,
        1 <= x <= n * m,
    ensures
        1 <= result.0 <= 1_000_000,
        1 <= result.1 <= 1_000_000,
        1 <= result.2 <= result.0 * result.1,
        result.0 == n,
        result.1 == m,
        result.2 == x,
{
    (n, m, x)
}

}

use std::io::Write;

struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0
    }
    fn gen_range_u64(&mut self, lo: u64, hi: u64) -> u64 {
        let r = hi - lo + 1;
        lo + self.next_u64() % r
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

fn build_input(cases: &[(u64, u64, u64)]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (n, m, x) in cases {
        s.push_str(&format!("{} {} {}\n", n, m, x));
    }
    s
}

fn build_output(answers: &[u64]) -> String {
    let mut s = String::new();
    for a in answers {
        s.push_str(&format!("{}\n", a));
    }
    s
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(31337);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    // boundaries
    {
        let cases: Vec<(u64, u64, u64)> = vec![
            (1, 1, 1),
            (1_000_000, 1_000_000, 1),
            (1_000_000, 1_000_000, 1_000_000_000_000),
            (1_000_000, 1, 1),
            (1, 1_000_000, 1_000_000),
        ];
        let answers: Vec<u64> = cases.iter().map(|&(n, m, x)| Solution::strange_table_number(n, m, x)).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }

    while count < target {
        let t: usize = match count % 5 {
            0 => 1,
            1 => rng.gen_range_usize(2, 10),
            2 => rng.gen_range_usize(10, 100),
            3 => rng.gen_range_usize(100, 1000),
            _ => rng.gen_range_usize(1000, 5000),
        };
        let mut cases: Vec<(u64, u64, u64)> = Vec::new();
        for _ in 0..t {
            let mode = rng.next_u64() % 5;
            let (n, m) = match mode {
                0 => (1, rng.gen_range_u64(1, 1_000_000)),
                1 => (rng.gen_range_u64(1, 1_000_000), 1),
                2 => (rng.gen_range_u64(1, 100), rng.gen_range_u64(1, 100)),
                3 => (rng.gen_range_u64(1, 10000), rng.gen_range_u64(1, 10000)),
                _ => (rng.gen_range_u64(1, 1_000_000), rng.gen_range_u64(1, 1_000_000)),
            };
            let total = n.saturating_mul(m).max(1);
            let x = rng.gen_range_u64(1, total);
            cases.push((n, m, x));
        }
        let answers: Vec<u64> = cases.iter().map(|&(n, m, x)| Solution::strange_table_number(n, m, x)).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

