use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    base: i64,
    d1: i64,
    d2: i64,
    d3: i64,
    mutation_kind: u8,
) -> (result: (i64, i64, i64, i64))
    requires
        1 <= base <= 91,
        1 <= d1 <= 3,
        1 <= d2 <= 3,
        1 <= d3 <= 3,
    ensures
        1 <= result.0 <= 100,
        1 <= result.1 <= 100,
        1 <= result.2 <= 100,
        1 <= result.3 <= 100,
        result.0 != result.1,
        result.0 != result.2,
        result.0 != result.3,
        result.1 != result.2,
        result.1 != result.3,
        result.2 != result.3,
{
    if mutation_kind == 0 {
        // ascending: s1 < s2 < s3 < s4
        let s1 = base;
        let s2 = base + d1;
        let s3 = base + d1 + d2;
        let s4 = base + d1 + d2 + d3;
        (s1, s2, s3, s4)
    } else if mutation_kind == 1 {
        // descending: s1 > s2 > s3 > s4
        let s4 = base;
        let s3 = base + d1;
        let s2 = base + d1 + d2;
        let s1 = base + d1 + d2 + d3;
        (s1, s2, s3, s4)
    } else if mutation_kind == 2 {
        // swap pairs: strongest in different semis
        let s3 = base;
        let s4 = base + d1;
        let s1 = base + d1 + d2;
        let s2 = base + d1 + d2 + d3;
        (s1, s2, s3, s4)
    } else if mutation_kind == 3 {
        // interleaved: s1 < s3 < s2 < s4
        let s1 = base;
        let s3 = base + d1;
        let s2 = base + d1 + d2;
        let s4 = base + d1 + d2 + d3;
        (s1, s2, s3, s4)
    } else if mutation_kind == 4 {
        // reverse interleave: s2 < s4 < s1 < s3
        let s2 = base;
        let s4 = base + d1;
        let s1 = base + d1 + d2;
        let s3 = base + d1 + d2 + d3;
        (s1, s2, s3, s4)
    } else {
        // default: ascending
        let s1 = base;
        let s2 = base + d1;
        let s3 = base + d1 + d2;
        let s4 = base + d1 + d2 + d3;
        (s1, s2, s3, s4)
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

fn build_input(cases: &[(i64, i64, i64, i64)]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (a, b, c, d) in cases {
        s.push_str(&format!("{} {} {} {}\n", a, b, c, d));
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

fn make_distinct(rng: &mut Rng) -> (i64, i64, i64, i64) {
    loop {
        let s1 = rng.gen_range_i64(1, 100);
        let s2 = rng.gen_range_i64(1, 100);
        let s3 = rng.gen_range_i64(1, 100);
        let s4 = rng.gen_range_i64(1, 100);
        let mut set = HashSet::new();
        set.insert(s1); set.insert(s2); set.insert(s3); set.insert(s4);
        if set.len() == 4 { return (s1, s2, s3, s4); }
    }
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);

    // Examples
    {
        let cases: Vec<(i64, i64, i64, i64)> = vec![
            (3, 7, 9, 5),
            (4, 5, 6, 7),
            (1, 2, 3, 4),
            (7, 3, 5, 2),
            (9, 10, 2, 8),
        ];
        let answers: Vec<bool> = cases.iter().map(|&(a, b, c, d)| Solution::fair_playoff(a, b, c, d)).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
    }

    let mut count = 1usize;

    // edges
    let edges: Vec<(i64, i64, i64, i64)> = vec![
        (1, 2, 3, 4),
        (4, 3, 2, 1),
        (1, 3, 2, 4),
        (1, 4, 2, 3),
        (97, 98, 99, 100),
    ];
    for e in edges {
        if count >= target { break; }
        let cases = vec![e];
        let answers: Vec<bool> = cases.iter().map(|&(a, b, c, d)| Solution::fair_playoff(a, b, c, d)).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }

    while count < target {
        let t: usize = if count < 20 { 1 } else { rng.gen_range_usize(2, 30) };
        let mut cases: Vec<(i64, i64, i64, i64)> = Vec::new();
        for _ in 0..t {
            cases.push(make_distinct(&mut rng));
        }
        let answers: Vec<bool> = cases.iter().map(|&(a, b, c, d)| Solution::fair_playoff(a, b, c, d)).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

