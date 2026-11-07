use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    seed_r: i64, seed_b: i64, seed_d: i64, mutation_kind: u8,
) -> (result: (i64, i64, i64))
    requires
        1 <= seed_r <= 1_000_000_000,
        1 <= seed_b <= 1_000_000_000,
        0 <= seed_d <= 1_000_000_000,
    ensures
        1 <= result.0 <= 1_000_000_000,
        1 <= result.1 <= 1_000_000_000,
        0 <= result.2 <= 1_000_000_000,
{
    let r: i64;
    let b: i64;
    let d: i64;

    if mutation_kind == 0 {
        // identity
        r = seed_r;
        b = seed_b;
        d = seed_d;
    } else if mutation_kind == 1 && seed_r < 1_000_000_000 {
        // nudge r up
        r = seed_r + 1;
        b = seed_b;
        d = seed_d;
    } else if mutation_kind == 2 && seed_r > 1 {
        // nudge r down
        r = seed_r - 1;
        b = seed_b;
        d = seed_d;
    } else if mutation_kind == 3 && seed_b < 1_000_000_000 {
        // nudge b up
        r = seed_r;
        b = seed_b + 1;
        d = seed_d;
    } else if mutation_kind == 4 && seed_b > 1 {
        // nudge b down
        r = seed_r;
        b = seed_b - 1;
        d = seed_d;
    } else if mutation_kind == 5 && seed_d < 1_000_000_000 {
        // nudge d up
        r = seed_r;
        b = seed_b;
        d = seed_d + 1;
    } else if mutation_kind == 6 && seed_d > 0 {
        // nudge d down
        r = seed_r;
        b = seed_b;
        d = seed_d - 1;
    } else if mutation_kind == 7 {
        // min boundary for r
        r = 1;
        b = seed_b;
        d = seed_d;
    } else if mutation_kind == 8 {
        // max boundary for r
        r = 1_000_000_000;
        b = seed_b;
        d = seed_d;
    } else if mutation_kind == 9 {
        // min boundary for b
        r = seed_r;
        b = 1;
        d = seed_d;
    } else if mutation_kind == 10 {
        // max boundary for b
        r = seed_r;
        b = 1_000_000_000;
        d = seed_d;
    } else if mutation_kind == 11 {
        // min boundary for d (d = 0)
        r = seed_r;
        b = seed_b;
        d = 0;
    } else if mutation_kind == 12 {
        // max boundary for d
        r = seed_r;
        b = seed_b;
        d = 1_000_000_000;
    } else if mutation_kind == 13 {
        // r = b (symmetric case)
        r = seed_r;
        b = seed_r;
        d = seed_d;
    } else if mutation_kind == 14 {
        // halve r
        let hr = seed_r / 2;
        r = if hr >= 1 { hr } else { 1 };
        b = seed_b;
        d = seed_d;
    } else if mutation_kind == 15 {
        // halve b
        r = seed_r;
        let hb = seed_b / 2;
        b = if hb >= 1 { hb } else { 1 };
        d = seed_d;
    } else if mutation_kind == 16 {
        // halve d
        r = seed_r;
        b = seed_b;
        d = seed_d / 2;
    } else if mutation_kind == 17 {
        // all min
        r = 1;
        b = 1;
        d = 0;
    } else if mutation_kind == 18 {
        // all max
        r = 1_000_000_000;
        b = 1_000_000_000;
        d = 1_000_000_000;
    } else if mutation_kind == 19 {
        // double r (clamped)
        r = if seed_r <= 500_000_000 { seed_r * 2 } else { 1_000_000_000 };
        b = seed_b;
        d = seed_d;
    } else if mutation_kind == 20 {
        // double b (clamped)
        r = seed_r;
        b = if seed_b <= 500_000_000 { seed_b * 2 } else { 1_000_000_000 };
        d = seed_d;
    } else {
        // fallback: identity
        r = seed_r;
        b = seed_b;
        d = seed_d;
    }

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
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);

    // Examples
    {
        let cases: Vec<(i64, i64, i64)> = vec![
            (1, 1, 0), (2, 7, 3), (6, 1, 4), (5, 4, 0),
        ];
        let answers: Vec<bool> = cases.iter().map(|&(r, b, d)| Solution::beans_distributable(r, b, d)).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
    }

    let mut count = 1usize;

    let edges: Vec<(i64, i64, i64)> = vec![
        (1, 1, 0),
        (1, 1_000_000_000, 0),
        (1, 1_000_000_000, 1_000_000_000),
        (1_000_000_000, 1, 0),
        (1_000_000_000, 1_000_000_000, 0),
        (1, 2, 1),
        (2, 1, 1),
    ];
    for e in edges {
        if count >= target { break; }
        let cases = vec![e];
        let answers: Vec<bool> = cases.iter().map(|&(r, b, d)| Solution::beans_distributable(r, b, d)).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }

    while count < target {
        let t: usize = if count < 20 { 1 } else { rng.gen_range_usize(2, 30) };
        let mut cases: Vec<(i64, i64, i64)> = Vec::new();
        for _ in 0..t {
            let mode = rng.next_u64() % 4;
            let (r, b, d) = match mode {
                0 => (rng.gen_range_i64(1, 10), rng.gen_range_i64(1, 10), rng.gen_range_i64(0, 10)),
                1 => (rng.gen_range_i64(1, 1000), rng.gen_range_i64(1, 1000), rng.gen_range_i64(0, 1000)),
                2 => (rng.gen_range_i64(1, 1_000_000), rng.gen_range_i64(1, 1_000_000), rng.gen_range_i64(0, 1_000_000)),
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

