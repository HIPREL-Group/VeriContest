use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_a: i64, seed_b: i64, seed_c: i64, mutation_kind: u8) -> (result: (i64, i64, i64))
    requires
        1 <= seed_a <= 1_000_000_000,
        1 <= seed_b <= 1_000_000_000,
        1 <= seed_c <= 1_000_000_000,
    ensures
        1 <= result.0 <= 1_000_000_000,
        1 <= result.1 <= 1_000_000_000,
        1 <= result.2 <= 1_000_000_000,
{
    if mutation_kind == 0 {
        // identity
        (seed_a, seed_b, seed_c)
    } else if mutation_kind == 1 {
        // a = b (equal case, c decides)
        (seed_b, seed_b, seed_c)
    } else if mutation_kind == 2 {
        // a > b (first wins)
        if seed_a > seed_b {
            (seed_a, seed_b, seed_c)
        } else {
            (seed_b, seed_a, seed_c)
        }
    } else if mutation_kind == 3 {
        // a < b (second wins)
        if seed_a < seed_b {
            (seed_a, seed_b, seed_c)
        } else {
            (seed_b, seed_a, seed_c)
        }
    } else if mutation_kind == 4 {
        // all equal
        (seed_a, seed_a, seed_a)
    } else if mutation_kind == 5 {
        // boundary: a = 1
        (1, seed_b, seed_c)
    } else if mutation_kind == 6 {
        // boundary: b = 1
        (seed_a, 1, seed_c)
    } else if mutation_kind == 7 {
        // boundary: c = 1 (odd, first wins when a == b)
        (seed_a, seed_b, 1)
    } else if mutation_kind == 8 {
        // boundary: c = 2 (even, second wins when a == b)
        (seed_a, seed_b, 2)
    } else if mutation_kind == 9 {
        // boundary: a = b = 1, c = 1
        (1, 1, 1)
    } else if mutation_kind == 10 {
        // boundary: max values
        (1_000_000_000, 1_000_000_000, 1_000_000_000)
    } else if mutation_kind == 11 {
        // nudge a up
        if seed_a < 1_000_000_000 {
            (seed_a + 1, seed_b, seed_c)
        } else {
            (seed_a, seed_b, seed_c)
        }
    } else if mutation_kind == 12 {
        // nudge b up
        if seed_b < 1_000_000_000 {
            (seed_a, seed_b + 1, seed_c)
        } else {
            (seed_a, seed_b, seed_c)
        }
    } else if mutation_kind == 13 {
        // nudge c up
        if seed_c < 1_000_000_000 {
            (seed_a, seed_b, seed_c + 1)
        } else {
            (seed_a, seed_b, seed_c)
        }
    } else if mutation_kind == 14 {
        // nudge a down
        if seed_a > 1 {
            (seed_a - 1, seed_b, seed_c)
        } else {
            (seed_a, seed_b, seed_c)
        }
    } else if mutation_kind == 15 {
        // nudge b down
        if seed_b > 1 {
            (seed_a, seed_b - 1, seed_c)
        } else {
            (seed_a, seed_b, seed_c)
        }
    } else if mutation_kind == 16 {
        // nudge c down
        if seed_c > 1 {
            (seed_a, seed_b, seed_c - 1)
        } else {
            (seed_a, seed_b, seed_c)
        }
    } else if mutation_kind == 17 {
        // halve a
        let ha = seed_a / 2;
        if ha >= 1 { (ha, seed_b, seed_c) } else { (1, seed_b, seed_c) }
    } else if mutation_kind == 18 {
        // halve b
        let hb = seed_b / 2;
        if hb >= 1 { (seed_a, hb, seed_c) } else { (seed_a, 1, seed_c) }
    } else if mutation_kind == 19 {
        // halve c
        let hc = seed_c / 2;
        if hc >= 1 { (seed_a, seed_b, hc) } else { (seed_a, seed_b, 1) }
    } else {
        // fallback: identity
        (seed_a, seed_b, seed_c)
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

type Case = (i64, i64, i64);

fn build_input(cases: &[Case]) -> String {
    let mut s = format!("{}\n", cases.len());
    for &(a, b, c) in cases {
        s.push_str(&format!("{} {} {}\n", a, b, c));
    }
    s
}

fn build_output(answers: &[bool]) -> String {
    let mut s = String::new();
    for &a in answers {
        s.push_str(if a {"First\n"} else {"Second\n"});
    }
    s
}

fn solve(c: Case) -> bool {
    Solution::first_wins(c.0, c.1, c.2)
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(1858);
    let mut seen: HashSet<String> = HashSet::new();

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    // Example
    let example: Vec<Case> = vec![(1, 1, 1), (9, 3, 3), (1, 2, 3), (6, 6, 9), (2, 2, 8)];
    {
        let inp = build_input(&example);
        let answers: Vec<bool> = example.iter().map(|&c| solve(c)).collect();
        let outs = build_output(&answers);
        if seen.insert(inp.clone()) {
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
            count += 1;
        }
    }

    // Edge cases
    let edges: Vec<Case> = vec![
        (1, 1, 1),
        (1_000_000_000, 1, 1),
        (1, 1_000_000_000, 1),
        (1, 1, 1_000_000_000),
        (1_000_000_000, 1_000_000_000, 1_000_000_000),
        (5, 5, 1),
        (5, 5, 2),
    ];
    for &ec in &edges {
        if count >= target { break; }
        let cases = vec![ec];
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<bool> = cases.iter().map(|&c| solve(c)).collect();
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }

    // Bundled
    while count < target {
        let t: usize = if count < 30 { rng.gen_range_usize(2, 8) } else { rng.gen_range_usize(5, 30) };
        let mut cases: Vec<Case> = Vec::new();
        for _ in 0..t {
            let scale = match rng.next_u64() % 4 {
                0 => 10i64,
                1 => 1000,
                2 => 1_000_000,
                _ => 1_000_000_000,
            };
            cases.push((rng.gen_range_i64(1, scale), rng.gen_range_i64(1, scale), rng.gen_range_i64(1, scale)));
        }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<bool> = cases.iter().map(|&c| solve(c)).collect();
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}

