use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    seed_a: i64,
    seed_b: i64,
    seed_c: i64,
    mutation_kind: u8,
) -> (result: (i64, i64, i64))
    requires
        0 <= seed_a <= 20,
        0 <= seed_b <= 20,
        0 <= seed_c <= 20,
    ensures
        0 <= result.0 <= 20,
        0 <= result.1 <= 20,
        0 <= result.2 <= 20,
{
    if mutation_kind == 0 {
        // identity
        (seed_a, seed_b, seed_c)
    } else if mutation_kind == 1 && seed_a < 20 {
        // nudge a up
        (seed_a + 1, seed_b, seed_c)
    } else if mutation_kind == 2 && seed_a > 0 {
        // nudge a down
        (seed_a - 1, seed_b, seed_c)
    } else if mutation_kind == 3 && seed_b < 20 {
        // nudge b up
        (seed_a, seed_b + 1, seed_c)
    } else if mutation_kind == 4 && seed_c < 20 {
        // nudge c up
        (seed_a, seed_b, seed_c + 1)
    } else if mutation_kind == 5 {
        // zero a
        (0, seed_b, seed_c)
    } else if mutation_kind == 6 {
        // zero all
        (0, 0, 0)
    } else if mutation_kind == 7 {
        // max boundary
        (20, 20, 20)
    } else if mutation_kind == 8 {
        // a = b + c if it fits
        let s = seed_b + seed_c;
        if s <= 20 {
            (s, seed_b, seed_c)
        } else {
            (seed_a, seed_b, seed_c)
        }
    } else if mutation_kind == 9 {
        // halve a
        (seed_a / 2, seed_b, seed_c)
    } else if mutation_kind == 10 {
        // double a if fits
        if seed_a <= 10 {
            (seed_a * 2, seed_b, seed_c)
        } else {
            (seed_a, seed_b, seed_c)
        }
    } else if mutation_kind == 11 {
        // swap a and b
        (seed_b, seed_a, seed_c)
    } else if mutation_kind == 12 {
        // rotate: (b, c, a)
        (seed_b, seed_c, seed_a)
    } else {
        // fallback
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

type TC = (i64, i64, i64);

fn build_input(cases: &[TC]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (a, b, c) in cases {
        s.push_str(&format!("{} {} {}\n", a, b, c));
    }
    s
}

fn build_output(cases: &[TC]) -> String {
    let mut s = String::new();
    for (a, b, c) in cases {
        if Solution::one_is_sum_of_others(*a, *b, *c) {
            s.push_str("YES\n");
        } else {
            s.push_str("NO\n");
        }
    }
    s
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(1742);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let examples: Vec<TC> = vec![
        (1, 4, 3),
        (2, 5, 8),
        (9, 11, 20),
        (0, 0, 0),
        (20, 20, 20),
        (4, 12, 3),
        (15, 7, 8),
        (0, 0, 1),
        (10, 10, 0),
    ];

    for ex in &examples {
        if count >= target { break; }
        let cases = vec![ex.clone()];
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let outs = build_output(&cases);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }

    while count < target {
        let t: usize = if count < 20 { rng.gen_range_usize(1, 5) } else { rng.gen_range_usize(2, 50) };
        let mut cases: Vec<TC> = Vec::new();
        for _ in 0..t {
            // sometimes generate "yes" cases by setting c=a+b
            let force_yes = rng.next_u64() % 3 == 0;
            let a = rng.gen_range_i64(0, 20);
            let b = rng.gen_range_i64(0, 20);
            let c = if force_yes {
                let s = a + b;
                if s <= 20 { s } else { rng.gen_range_i64(0, 20) }
            } else {
                rng.gen_range_i64(0, 20)
            };
            cases.push((a, b, c));
        }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let outs = build_output(&cases);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}

