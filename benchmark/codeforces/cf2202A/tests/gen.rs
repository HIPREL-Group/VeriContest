use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_x: i64, seed_y: i64, mutation_kind: u8) -> (result: (i64, i64))
    requires
        1 <= seed_x as int <= 1_000_000_000,
        -100_000_000 <= seed_y as int <= 100_000_000,
    ensures
        1 <= result.0 as int <= 1_000_000_000,
        -100_000_000 <= result.1 as int <= 100_000_000,
{
    if mutation_kind == 0 {
        // identity
        (seed_x, seed_y)
    } else if mutation_kind == 1 && seed_x < 1_000_000_000 {
        // nudge x up
        (seed_x + 1, seed_y)
    } else if mutation_kind == 2 && seed_x > 1 {
        // nudge x down
        (seed_x - 1, seed_y)
    } else if mutation_kind == 3 && seed_y < 100_000_000 {
        // nudge y up
        (seed_x, seed_y + 1)
    } else if mutation_kind == 4 && seed_y > -100_000_000 {
        // nudge y down
        (seed_x, seed_y - 1)
    } else if mutation_kind == 5 {
        // y = 0
        (seed_x, 0)
    } else if mutation_kind == 6 {
        // x = 1 (min boundary)
        (1, seed_y)
    } else if mutation_kind == 7 {
        // x = max boundary
        (1_000_000_000, seed_y)
    } else if mutation_kind == 8 {
        // y = min boundary
        (seed_x, -100_000_000)
    } else if mutation_kind == 9 {
        // y = max boundary
        (seed_x, 100_000_000)
    } else if mutation_kind == 10 {
        // halve x
        let hx = seed_x / 2;
        if hx >= 1 {
            (hx, seed_y)
        } else {
            (1, seed_y)
        }
    } else if mutation_kind == 11 {
        // double x (clamped)
        if seed_x <= 500_000_000 {
            (seed_x * 2, seed_y)
        } else {
            (1_000_000_000, seed_y)
        }
    } else if mutation_kind == 12 {
        // negate y (if in range)
        if seed_y > -100_000_000 && seed_y < 100_000_000 {
            (seed_x, -seed_y)
        } else if seed_y == -100_000_000 {
            (seed_x, 100_000_000)
        } else {
            (seed_x, -100_000_000)
        }
    } else if mutation_kind == 13 {
        // absolute value of y
        if seed_y >= 0 {
            (seed_x, seed_y)
        } else {
            if seed_y > -100_000_000 {
                (seed_x, -seed_y)
            } else {
                (seed_x, 100_000_000)
            }
        }
    } else {
        // fallback: identity
        (seed_x, seed_y)
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

fn build_input_multi(cases: &[(i64, i64)]) -> String {
    let mut s = format!("{}\n", cases.len());
    for &(x, y) in cases {
        s.push_str(&format!("{} {}\n", x, y));
    }
    s
}

fn build_output_multi(answers: &[bool]) -> String {
    let mut s = String::new();
    for &a in answers {
        s.push_str(if a { "YES\n" } else { "NO\n" });
    }
    s
}

fn solve(x: i64, y: i64) -> bool {
    Solution::parkour_reachable(x, y)
}

fn random_case(rng: &mut Rng, mode: usize) -> (i64, i64) {
    let x = match mode {
        0 => rng.gen_range_i64(1, 10),
        1 => rng.gen_range_i64(1, 100),
        2 => rng.gen_range_i64(1, 10_000),
        3 => rng.gen_range_i64(1, 1_000_000),
        4 => rng.gen_range_i64(1, 1_000_000_000),
        _ => rng.gen_range_i64(1, 1000),
    };
    let y_max = (x / 2 + 1).min(100_000_000);
    let y = match mode % 3 {
        0 => rng.gen_range_i64(-y_max.min(100_000_000), y_max.min(100_000_000)),
        1 => rng.gen_range_i64(-100_000_000, 100_000_000),
        _ => rng.gen_range_i64(-(x.min(1000)), x.min(1000)),
    };
    (x, y)
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(2202);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let examples: Vec<(i64, i64)> = vec![
        (2, 1),
        (3, 0),
        (4, -1),
        (4, 1),
        (14, 1),
        (1, -4),
        (3, -1),
        (2, 102),
        (4, -12),
        (4, -3),
        (8, 4),
    ];
    {
        let answers: Vec<bool> = examples.iter().map(|&(x, y)| solve(x, y)).collect();
        let inp = build_input_multi(&examples);
        let outp = build_output_multi(&answers);
        if seen.insert(inp.clone()) {
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
            count += 1;
        }
    }

    for &ex in &examples {
        if count >= target { break; }
        let cases = vec![ex];
        let answers: Vec<bool> = cases.iter().map(|&(x, y)| solve(x, y)).collect();
        let inp = build_input_multi(&cases);
        let outp = build_output_multi(&answers);
        if seen.insert(inp.clone()) {
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
            count += 1;
        }
    }

    let edges: Vec<(i64, i64)> = vec![
        (1, 0),
        (2, 0),
        (3, 0),
        (1, 1),
        (1, -1),
        (1_000_000_000, 100_000_000),
        (1_000_000_000, -100_000_000),
        (1_000_000_000, 0),
    ];
    for chunk in edges.chunks(3) {
        if count >= target { break; }
        let cases: Vec<(i64, i64)> = chunk.to_vec();
        let answers: Vec<bool> = cases.iter().map(|&(x, y)| solve(x, y)).collect();
        let inp = build_input_multi(&cases);
        let outp = build_output_multi(&answers);
        if seen.insert(inp.clone()) {
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
            count += 1;
        }
    }

    while count < target {
        let t: usize = if count < 30 { rng.gen_range_usize(1, 5) } else { rng.gen_range_usize(2, 30) };
        let mut cases: Vec<(i64, i64)> = Vec::with_capacity(t);
        for _ in 0..t {
            let mode = rng.gen_range_usize(0, 5);
            cases.push(random_case(&mut rng, mode));
        }
        let answers: Vec<bool> = cases.iter().map(|&(x, y)| solve(x, y)).collect();
        let inp = build_input_multi(&cases);
        let outp = build_output_multi(&answers);
        if !seen.insert(inp.clone()) { continue; }
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

