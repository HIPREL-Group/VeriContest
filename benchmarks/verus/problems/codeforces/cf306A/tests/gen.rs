use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: u32, m: u32, mutation_kind: u8) -> (result: (u32, u32))
    requires
        1 <= m <= n <= 100,
    ensures
        1 <= result.1 <= result.0 <= 100,
{
    if mutation_kind == 0 {
        (n, m)
    } else if mutation_kind == 1 {
        (n, 1u32)
    } else if mutation_kind == 2 {
        (n, n)
    } else if mutation_kind == 3 && n < 100 {
        (n + 1, m)
    } else {
        (n, m)
    }
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
    fn gen_range_u32(&mut self, lo: u32, hi: u32) -> u32 {
        lo + (self.next_u64() as u32) % (hi - lo + 1)
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

fn build_input(n: u32, m: u32) -> String {
    format!("{} {}\n", n, m)
}

fn build_output(ans: &Vec<u32>) -> String {
    let parts: Vec<String> = ans.iter().map(|v| v.to_string()).collect();
    format!("{}\n", parts.join(" "))
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(306);
    let mut seen: HashSet<(u32, u32)> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |n: u32, m: u32, seen: &mut HashSet<(u32, u32)>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if !(1 <= m && m <= n && n <= 100) { return; }
        if !seen.insert((n, m)) { return; }
        let inp = build_input(n, m);
        let ans = Solution::distribute(n, m);
        let outp = build_output(&ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    // Sample tests
    emit(12, 3, &mut seen, &mut out, &mut count);
    emit(15, 4, &mut seen, &mut out, &mut count);
    emit(18, 7, &mut seen, &mut out, &mut count);

    // Boundary
    emit(1, 1, &mut seen, &mut out, &mut count);
    emit(100, 1, &mut seen, &mut out, &mut count);
    emit(100, 100, &mut seen, &mut out, &mut count);
    emit(100, 50, &mut seen, &mut out, &mut count);
    emit(2, 1, &mut seen, &mut out, &mut count);
    emit(2, 2, &mut seen, &mut out, &mut count);

    // Random
    let mut tries = 0usize;
    while count < target && tries < target * 200 {
        tries += 1;
        let n = rng.gen_range_u32(1, 100);
        let m = rng.gen_range_u32(1, n);
        emit(n, m, &mut seen, &mut out, &mut count);
    }
}
