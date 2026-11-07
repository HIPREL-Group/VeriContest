use vstd::prelude::*;

verus! {

pub fn generate_test_case(a: i64, b: i64, c: i64) -> (result: (i64, i64, i64))
    requires
        1 <= a <= 1_000_000_000,
        1 <= b <= 1_000_000_000,
        1 <= c <= 1_000_000_000,
    ensures
        1 <= result.0 <= 1_000_000_000,
        1 <= result.1 <= 1_000_000_000,
        1 <= result.2 <= 1_000_000_000,
{
    (a, b, c)
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

type Case = (i64, i64, i64);

fn build_input(cases: &[Case]) -> String {
    let mut s = format!("{}\n", cases.len());
    for &(a, b, c) in cases {
        s.push_str(&format!("{} {} {}\n", a, b, c));
    }
    s
}

fn build_output(answers: &[bool]) -> String {
    let mut s = String::new();
    for &a in answers {
        s.push_str(if a {"First\n"} else {"Second\n"});
    }
    s
}

fn solve(c: Case) -> bool {
    Solution::first_wins(c.0, c.1, c.2)
}

fn pick_adv(rng: &mut Rng) -> Case {
    match rng.next_u64() % 6 {
        0 => (rng.gen_range_i64(1, 1_000_000_000), rng.gen_range_i64(1, 1_000_000_000), rng.gen_range_i64(1, 1_000_000_000)),
        1 => {
            // a == b
            let v = rng.gen_range_i64(1, 1_000_000_000);
            (v, v, rng.gen_range_i64(1, 1_000_000_000))
        }
        2 => (1_000_000_000, 1_000_000_000, 1_000_000_000),
        3 => (1, 1, 1),
        4 => {
            // a > b
            let b = rng.gen_range_i64(1, 999_999_999);
            (b + rng.gen_range_i64(1, 1_000_000_000 - b), b, rng.gen_range_i64(1, 1_000_000_000))
        }
        _ => {
            // a < b
            let a = rng.gen_range_i64(1, 999_999_999);
            (a, a + rng.gen_range_i64(1, 1_000_000_000 - a), rng.gen_range_i64(1, 1_000_000_000))
        }
    }
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(31415);
    let mut seen: HashSet<String> = HashSet::new();

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    while count < target {
        let t: usize = if count < 30 { rng.gen_range_usize(10, 30) } else { rng.gen_range_usize(20, 100) };
        let mut cases: Vec<Case> = Vec::new();
        for _ in 0..t {
            cases.push(pick_adv(&mut rng));
        }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<bool> = cases.iter().map(|&c| solve(c)).collect();
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}

