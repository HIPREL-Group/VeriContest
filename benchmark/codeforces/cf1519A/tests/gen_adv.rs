use vstd::prelude::*;

verus! {

pub fn generate_test_case(r: i64, b: i64, d: i64) -> (res: (i64, i64, i64))
    requires
        1 <= r <= 1_000_000_000,
        1 <= b <= 1_000_000_000,
        0 <= d <= 1_000_000_000,
    ensures
        1 <= res.0 <= 1_000_000_000,
        1 <= res.1 <= 1_000_000_000,
        0 <= res.2 <= 1_000_000_000,
{
    (r, b, d)
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
    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let r = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % r) as i128) as i64
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

fn build_input(cases: &[(i64, i64, i64)]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (r, b, d) in cases {
        s.push_str(&format!("{} {} {}\n", r, b, d));
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
    let mut rng = Rng::new(31337);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    // boundaries
    {
        let cases: Vec<(i64, i64, i64)> = vec![
            (1, 1, 0),
            (1_000_000_000, 1_000_000_000, 0),
            (1, 1_000_000_000, 0),
            (1_000_000_000, 1, 0),
            (1, 1_000_000_000, 1_000_000_000),
            (1_000_000_000, 1, 1_000_000_000),
        ];
        let answers: Vec<bool> = cases.iter().map(|&(r, b, d)| Solution::beans_distributable(r, b, d)).collect();
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
            3 => rng.gen_range_usize(100, 500),
            _ => rng.gen_range_usize(500, 1000),
        };
        let mut cases: Vec<(i64, i64, i64)> = Vec::new();
        for _ in 0..t {
            let mode = rng.next_u64() % 6;
            let (r, b, d) = match mode {
                0 => { let v = rng.gen_range_i64(1, 1_000_000_000); (v, v, 0) },
                1 => (rng.gen_range_i64(1, 100), rng.gen_range_i64(1, 100), rng.gen_range_i64(0, 100)),
                2 => (1, rng.gen_range_i64(1, 1_000_000_000), rng.gen_range_i64(0, 1_000_000_000)),
                3 => (rng.gen_range_i64(1, 1_000_000_000), 1, rng.gen_range_i64(0, 1_000_000_000)),
                4 => { let r = rng.gen_range_i64(1, 1_000_000_000); (r, r, rng.gen_range_i64(0, 1_000_000_000)) },
                _ => (rng.gen_range_i64(1, 1_000_000_000), rng.gen_range_i64(1, 1_000_000_000), rng.gen_range_i64(0, 1_000_000_000)),
            };
            cases.push((r, b, d));
        }
        let answers: Vec<bool> = cases.iter().map(|&(r, b, d)| Solution::beans_distributable(r, b, d)).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

