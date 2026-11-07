use vstd::prelude::*;

verus! {

pub fn generate_test_case(x: u64) -> (result: u64)
    requires
        1 <= x <= 1_000_000,
    ensures
        1 <= result <= 1_000_000,
{
    x
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
    fn gen_range_u64(&mut self, lo: u64, hi: u64) -> u64 {
        lo + self.next_u64() % (hi - lo + 1)
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

fn build_input(x: u64) -> String { format!("{}\n", x) }
fn build_output(ans: u64) -> String { format!("{}\n", ans) }

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(61701);
    let mut seen: HashSet<u64> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |x: u64, seen: &mut HashSet<u64>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if x < 1 || x > 1_000_000 { return; }
        if !seen.insert(x) { return; }
        let inp = build_input(x);
        let ans = Solution::min_steps(x);
        let outs = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    // Boundaries
    for x in 1..=20u64 { emit(x, &mut seen, &mut out, &mut count); }
    for k in 1..=200u64 {
        emit(5 * k - 1, &mut seen, &mut out, &mut count);
        emit(5 * k, &mut seen, &mut out, &mut count);
        emit(5 * k + 1, &mut seen, &mut out, &mut count);
        if count >= target { break; }
    }
    // Near max
    for x in (999_980..=1_000_000u64).rev() {
        emit(x, &mut seen, &mut out, &mut count);
    }

    while count < target {
        let x = rng.gen_range_u64(1, 1_000_000);
        emit(x, &mut seen, &mut out, &mut count);
    }
}

