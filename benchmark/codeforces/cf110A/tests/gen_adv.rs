use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: u64) -> (result: u64)
    requires
        1 <= seed <= 1_000_000_000_000_000_000u64,
    ensures
        1 <= result <= 1_000_000_000_000_000_000u64,
{
    seed
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

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(110);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut seen: HashSet<String> = HashSet::new();
    let mut count = 0usize;

    let mut emit = |inp: String, n: u64, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if n < 1 || n > 1_000_000_000_000_000_000u64 { return; }
        if !seen.insert(inp.clone()) { return; }
        let result = Solution::nearly_lucky(n);
        let outp = if result { "YES\n".to_string() } else { "NO\n".to_string() };
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    // Edge cases
    for &n in &[1u64, 4, 7, 44, 47, 74, 77, 444, 447, 477, 747, 4444444, 7777777, 4747474,
                7474747, 444477, 447777, 477477, 47, 1_000_000_000_000_000_000u64,
                999_999_999_999_999_999u64, 47474747474747u64,
                40047, 7747774, 100, 1000, 10000, 47000000000000000u64] {
        emit(format!("{}\n", n), n, &mut seen, &mut out, &mut count);
    }

    // Whitespace variants
    for &n in &[4u64, 7, 47, 74, 4747, 7747774, 1_000_000_000_000_000_000u64] {
        emit(format!("{}", n), n, &mut seen, &mut out, &mut count);
        emit(format!(" {} \n", n), n, &mut seen, &mut out, &mut count);
        emit(format!("{}\r\n", n), n, &mut seen, &mut out, &mut count);
    }

    while count < target {
        let n = (rng.next_u64() % 1_000_000_000_000_000_000u64) + 1;
        emit(format!("{}\n", n), n, &mut seen, &mut out, &mut count);
    }
}
