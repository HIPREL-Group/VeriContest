use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_a: u8, seed_b: u8, seed_c: u8, seed_d: u8, mutation_kind: u8) -> (res: (u8, u8, u8, u8))
    requires
        seed_a < 26,
        seed_b < 26,
        seed_c < 26,
        seed_d < 26,
    ensures
        res.0 < 26,
        res.1 < 26,
        res.2 < 26,
        res.3 < 26,
{
    let a: u8 = if mutation_kind == 0 {
        seed_a                                          // identity
    } else if mutation_kind == 1 && seed_a < 25 {
        (seed_a + 1) as u8                              // nudge up
    } else if mutation_kind == 2 && seed_a > 0 {
        (seed_a - 1) as u8                              // nudge down
    } else if mutation_kind == 3 {
        0u8                                             // zero (letter 'a')
    } else if mutation_kind == 4 {
        25u8                                            // max boundary (letter 'z')
    } else if mutation_kind == 5 {
        seed_b                                          // copy from b
    } else {
        seed_a                                          // fallback
    };

    let b: u8 = if mutation_kind == 6 {
        seed_a                                          // copy from a
    } else if mutation_kind == 7 && seed_b < 25 {
        (seed_b + 1) as u8                              // nudge up
    } else if mutation_kind == 8 && seed_b > 0 {
        (seed_b - 1) as u8                              // nudge down
    } else if mutation_kind == 9 {
        seed_c                                          // copy from c
    } else {
        seed_b                                          // fallback/identity
    };

    let c: u8 = if mutation_kind == 10 {
        seed_a                                          // all same as a
    } else if mutation_kind == 11 && seed_c < 25 {
        (seed_c + 1) as u8                              // nudge up
    } else if mutation_kind == 12 && seed_c > 0 {
        (seed_c - 1) as u8                              // nudge down
    } else {
        seed_c                                          // fallback/identity
    };

    let d: u8 = if mutation_kind == 13 {
        seed_a                                          // all same as a
    } else if mutation_kind == 14 {
        seed_b                                          // copy from b
    } else if mutation_kind == 15 && seed_d < 25 {
        (seed_d + 1) as u8                              // nudge up
    } else if mutation_kind == 16 && seed_d > 0 {
        (seed_d - 1) as u8                              // nudge down
    } else {
        seed_d                                          // fallback/identity
    };

    (a, b, c, d)
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

// Each case is 4 chars representing the 2x2 image (top-left, top-right, bottom-left, bottom-right)
type TC = (char, char, char, char);

fn build_input(cases: &[TC]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (a, b, c, d) in cases {
        s.push(*a);
        s.push(*b);
        s.push('\n');
        s.push(*c);
        s.push(*d);
        s.push('\n');
    }
    s
}

fn build_output(cases: &[TC]) -> String {
    let mut s = String::new();
    for (a, b, c, d) in cases {
        let av = (*a as u8) - b'a';
        let bv = (*b as u8) - b'a';
        let cv = (*c as u8) - b'a';
        let dv = (*d as u8) - b'a';
        let ans = Solution::min_moves_to_uniform(av, bv, cv, dv);
        s.push_str(&format!("{}\n", ans));
    }
    s
}

fn random_letter(rng: &mut Rng) -> char {
    (b'a' + (rng.gen_range_usize(0, 25) as u8)) as char
}

fn random_case(rng: &mut Rng) -> TC {
    (random_letter(rng), random_letter(rng), random_letter(rng), random_letter(rng))
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(1721);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let examples: Vec<TC> = vec![
        ('r', 'b', 'b', 'r'),
        ('c', 'c', 'w', 'b'),
        ('a', 'a', 'a', 'a'),
        ('a', 'b', 'c', 'd'),
        ('a', 'b', 'a', 'b'),
        ('z', 'z', 'z', 'z'),
        ('a', 'a', 'a', 'b'),
        ('a', 'a', 'b', 'b'),
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
        let t: usize = if count < 20 { rng.gen_range_usize(1, 5) } else { rng.gen_range_usize(2, 30) };
        let mut cases: Vec<TC> = Vec::new();
        for _ in 0..t {
            cases.push(random_case(&mut rng));
        }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let outs = build_output(&cases);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}

