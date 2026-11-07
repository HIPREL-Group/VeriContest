use vstd::prelude::*;

verus! {

pub fn generate_test_case(m: u64, a: u64, b: u64, c: u64) -> (result: (u64, u64, u64, u64))
    requires
        1 <= m <= 100000000,
        1 <= a <= 100000000,
        1 <= b <= 100000000,
        1 <= c <= 100000000,
    ensures
        1 <= result.0 <= 100000000,
        1 <= result.1 <= 100000000,
        1 <= result.2 <= 100000000,
        1 <= result.3 <= 100000000,
{
    (m, a, b, c)
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

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(20440);
    let mut seen: HashSet<String> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |inp: String, m: u64, a: u64, b: u64, c: u64, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if !seen.insert(inp.clone()) { return; }
        let ans = Solution::max_monkeys(m, a, b, c);
        let outp = format!("{}\n", ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    while count < target {
        let m = rng.gen_range_u64(1, 100000000);
        let a = rng.gen_range_u64(1, 100000000);
        let b = rng.gen_range_u64(1, 100000000);
        let c = rng.gen_range_u64(1, 100000000);
        emit(format!("1\n{} {} {} {}\n", m, a, b, c), m, a, b, c, &mut seen, &mut out, &mut count);
    }
}
