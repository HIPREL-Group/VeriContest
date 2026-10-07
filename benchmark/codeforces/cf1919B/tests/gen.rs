use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: u64, mutation_kind: u8) -> (result: (i64, i64))
    ensures
        0 <= result.0 <= 5000,
        0 <= result.1 <= 5000,
{
    let p = (seed % 5001) as i64;
    let m = ((seed >> 17) % 5001) as i64;
    if mutation_kind == 0 {
        (p, m)
    } else if mutation_kind == 1 {
        (0, m)
    } else if mutation_kind == 2 {
        (p, 0)
    } else if mutation_kind == 3 {
        (p, p)
    } else if mutation_kind == 4 {
        (5000, 5000)
    } else if mutation_kind == 5 {
        (1, 0)
    } else if mutation_kind == 6 {
        (0, 1)
    } else if mutation_kind == 7 {
        (5000, 0)
    } else if mutation_kind == 8 {
        (0, 5000)
    } else {
        (p, m)
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

fn build_input(p: i64, m: i64, plus_first: bool) -> String {
    let n = (p + m) as usize;
    let mut s = String::with_capacity(n);
    if plus_first {
        for _ in 0..p { s.push('+'); }
        for _ in 0..m { s.push('-'); }
    } else {
        for _ in 0..m { s.push('-'); }
        for _ in 0..p { s.push('+'); }
    }
    if s.is_empty() { return String::new(); }
    format!("1\n{}\n{}\n", n, s)
}

fn main() {
    let target = 100usize;
    let mut rng = Rng::new(1919);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut seen: HashSet<String> = HashSet::new();
    let mut count = 0usize;
    let mut tries = 0;

    while count < target && tries < target * 200 {
        tries += 1;
        let kind = (rng.next_u64() % 10) as u8;
        let s = rng.next_u64();
        let (p, m) = generate_test_case(s, kind);
        if p + m == 0 { continue; }
        if p + m > 5000 { continue; }
        let plus_first = (rng.next_u64() & 1) == 1;
        let inp = build_input(p, m, plus_first);
        if inp.is_empty() { continue; }
        if !seen.insert(inp.clone()) { continue; }
        let ans = Solution::min_penalty(p, m);
        let outp = format!("{}\n", ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}
