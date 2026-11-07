use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    seed_x1: i64,
    seed_y1: i64,
    dx: i64,
    dy: i64,
    mutation_kind: u8,
) -> (res: (i64, i64, i64, i64))
    requires
        1 <= seed_x1 <= 1_000_000_000,
        1 <= seed_y1 <= 1_000_000_000,
        0 <= dx <= 1_000_000_000 - seed_x1,
        0 <= dy <= 1_000_000_000 - seed_y1,
    ensures
        1 <= res.0 <= res.2 <= 1_000_000_000,
        1 <= res.1 <= res.3 <= 1_000_000_000,
{
    let x1 = seed_x1;
    let y1 = seed_y1;
    let x2 = seed_x1 + dx;
    let y2 = seed_y1 + dy;

    if mutation_kind == 0 {
        // identity
        (x1, y1, x2, y2)
    } else if mutation_kind == 1 && x1 < x2 {
        // nudge x1 up by 1
        (x1 + 1, y1, x2, y2)
    } else if mutation_kind == 2 && x2 > x1 {
        // nudge x2 down by 1
        (x1, y1, x2 - 1, y2)
    } else if mutation_kind == 3 && y1 < y2 {
        // nudge y1 up by 1
        (x1, y1 + 1, x2, y2)
    } else if mutation_kind == 4 && y2 > y1 {
        // nudge y2 down by 1
        (x1, y1, x2, y2 - 1)
    } else if mutation_kind == 5 {
        // collapse x range: x1 == x2
        (x1, y1, x1, y2)
    } else if mutation_kind == 6 {
        // collapse y range: y1 == y2
        (x1, y1, x2, y1)
    } else if mutation_kind == 7 {
        // collapse both: single cell
        (x1, y1, x1, y1)
    } else if mutation_kind == 8 {
        // set x1 to 1 (minimum)
        (1, y1, x2, y2)
    } else if mutation_kind == 9 {
        // set y1 to 1 (minimum)
        (x1, 1, x2, y2)
    } else if mutation_kind == 10 && dx >= 2 {
        // halve dx
        (x1, y1, x1 + dx / 2, y2)
    } else if mutation_kind == 11 && dy >= 2 {
        // halve dy
        (x1, y1, x2, y1 + dy / 2)
    } else {
        // fallback: identity
        (x1, y1, x2, y2)
    }
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

fn build_input(cases: &[(i64, i64, i64, i64)]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (x1, y1, x2, y2) in cases {
        s.push_str(&format!("{} {} {} {}\n", x1, y1, x2, y2));
    }
    s
}

fn build_output(answers: &[i64]) -> String {
    let mut s = String::new();
    for a in answers {
        s.push_str(&format!("{}\n", a));
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
        let cases: Vec<(i64, i64, i64, i64)> = vec![
            (1, 1, 2, 2),
            (1, 2, 2, 4),
            (179, 1, 179, 100000),
            (5, 7, 5, 7),
        ];
        let answers: Vec<i64> = cases.iter().map(|&(x1, y1, x2, y2)| Solution::celex_distinct_sums(x1, y1, x2, y2)).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
    }

    let mut count = 1usize;

    // Edge singles
    let edges: Vec<(i64, i64, i64, i64)> = vec![
        (1, 1, 1, 1),
        (1, 1, 1_000_000_000, 1_000_000_000),
        (1, 1, 1_000_000_000, 1),
        (1, 1, 1, 1_000_000_000),
        (5, 5, 5, 5),
        (1, 1, 2, 2),
        (10, 20, 30, 40),
    ];
    for e in edges {
        if count >= target { break; }
        let answers = vec![Solution::celex_distinct_sums(e.0, e.1, e.2, e.3)];
        let inp = build_input(&[e]);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }

    while count < target {
        let t: usize = if count < 20 { 1 } else { rng.gen_range_usize(2, 30) };
        let mut cases: Vec<(i64, i64, i64, i64)> = Vec::new();
        for _ in 0..t {
            let mode = rng.next_u64() % 4;
            let (x1, y1, x2, y2) = match mode {
                0 => {
                    let x1 = rng.gen_range_i64(1, 10);
                    let y1 = rng.gen_range_i64(1, 10);
                    let x2 = rng.gen_range_i64(x1, 20);
                    let y2 = rng.gen_range_i64(y1, 20);
                    (x1, y1, x2, y2)
                }
                1 => {
                    let x1 = rng.gen_range_i64(1, 1000);
                    let y1 = rng.gen_range_i64(1, 1000);
                    let x2 = rng.gen_range_i64(x1, 2000);
                    let y2 = rng.gen_range_i64(y1, 2000);
                    (x1, y1, x2, y2)
                }
                2 => {
                    let x1 = rng.gen_range_i64(1, 1_000_000);
                    let y1 = rng.gen_range_i64(1, 1_000_000);
                    let x2 = rng.gen_range_i64(x1, 1_000_000_000);
                    let y2 = rng.gen_range_i64(y1, 1_000_000_000);
                    (x1, y1, x2, y2)
                }
                _ => {
                    let x1 = rng.gen_range_i64(1, 1_000_000_000);
                    let y1 = rng.gen_range_i64(1, 1_000_000_000);
                    let x2 = rng.gen_range_i64(x1, 1_000_000_000);
                    let y2 = rng.gen_range_i64(y1, 1_000_000_000);
                    (x1, y1, x2, y2)
                }
            };
            cases.push((x1, y1, x2, y2));
        }
        let answers: Vec<i64> = cases.iter().map(|&(x1, y1, x2, y2)| Solution::celex_distinct_sums(x1, y1, x2, y2)).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

