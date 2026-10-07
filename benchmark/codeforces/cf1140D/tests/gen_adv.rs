use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: u32) -> (result: u32)
    requires
        3 <= seed <= 500,
    ensures
        3 <= result <= 500,
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
    let mut rng = Rng::new(1140);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut seen: HashSet<String> = HashSet::new();
    let mut count = 0usize;

    let mut emit = |inp: String, n: u32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if n < 3 || n > 500 { return; }
        if !seen.insert(inp.clone()) { return; }
        let result = Solution::min_triangulation(n);
        let outp = format!("{}\n", result);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    for n in 3..=500u32 {
        emit(format!("{}\n", n), n, &mut seen, &mut out, &mut count);
        if count >= target { break; }
    }

    // Whitespace variants
    for &n in &[3u32, 4, 5, 100, 250, 499, 500] {
        emit(format!("{}", n), n, &mut seen, &mut out, &mut count);
        emit(format!(" {} ", n), n, &mut seen, &mut out, &mut count);
        emit(format!("\t{}\t\n", n), n, &mut seen, &mut out, &mut count);
        emit(format!("{}\r\n", n), n, &mut seen, &mut out, &mut count);
    }

    while count < target {
        let n = ((rng.next_u64() as u32) % 498) + 3;
        emit(format!("{}\n", n), n, &mut seen, &mut out, &mut count);
    }
}
