use vstd::prelude::*;

verus! {

pub fn generate_test_case(a: i64, b: i64) -> (res: (i64, i64))
    requires
        1 <= a <= 100,
        1 <= b <= 100,
    ensures
        1 <= res.0 <= 100,
        1 <= res.1 <= 100,
{
    (a, b)
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

fn build_input(a: i64, b: i64) -> String { format!("{} {}\n", a, b) }
fn build_output(x: i64, y: i64) -> String { format!("{} {}\n", x, y) }

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(58101);
    let mut seen: HashSet<String> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |a: i64, b: i64, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if a < 1 || a > 100 || b < 1 || b > 100 { return; }
        let key = format!("{} {}", a, b);
        if !seen.insert(key) { return; }
        let inp = build_input(a, b);
        let (x, y) = Solution::hipster_sock_days(a, b);
        let outs = build_output(x, y);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    // Boundary - all corners
    for &a in &[1i64, 2, 99, 100] {
        for &b in &[1i64, 2, 99, 100] {
            emit(a, b, &mut seen, &mut out, &mut count);
        }
    }
    // Diagonals (a == b)
    for a in 1..=100i64 {
        emit(a, a, &mut seen, &mut out, &mut count);
        if count >= target { break; }
    }
    // Off-by-one
    for d in 1..=20i64 {
        emit(d, d + 1, &mut seen, &mut out, &mut count);
        emit(d + 1, d, &mut seen, &mut out, &mut count);
    }

    while count < target {
        let a = rng.gen_range_i64(1, 100);
        let b = rng.gen_range_i64(1, 100);
        emit(a, b, &mut seen, &mut out, &mut count);
    }
}

