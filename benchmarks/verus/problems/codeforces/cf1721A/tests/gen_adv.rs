use vstd::prelude::*;

verus! {

pub fn generate_test_case(a: u8, b: u8, c: u8, d: u8) -> (result: (u8, u8, u8, u8))
    requires
        a < 26,
        b < 26,
        c < 26,
        d < 26,
    ensures
        result.0 < 26,
        result.1 < 26,
        result.2 < 26,
        result.3 < 26,
{
    (a, b, c, d)
}

}

use std::io::Write;
use std::collections::HashSet;

struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self { Self(seed.wrapping_add(1)) }
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

fn gen_case(rng: &mut Rng, mode: usize) -> TC {
    match mode {
        0 => {
            // all same
            let c = random_letter(rng);
            (c, c, c, c)
        }
        1 => {
            // two distinct
            let a = random_letter(rng);
            let b = loop {
                let l = random_letter(rng);
                if l != a { break l; }
            };
            (a, b, a, b)
        }
        2 => {
            // three distinct (one duplicated)
            let a = random_letter(rng);
            let b = loop {
                let l = random_letter(rng);
                if l != a { break l; }
            };
            let c = loop {
                let l = random_letter(rng);
                if l != a && l != b { break l; }
            };
            (a, b, c, a)
        }
        3 => {
            // all distinct
            let a = random_letter(rng);
            let b = loop {
                let l = random_letter(rng);
                if l != a { break l; }
            };
            let c = loop {
                let l = random_letter(rng);
                if l != a && l != b { break l; }
            };
            let d = loop {
                let l = random_letter(rng);
                if l != a && l != b && l != c { break l; }
            };
            (a, b, c, d)
        }
        _ => {
            (random_letter(rng), random_letter(rng), random_letter(rng), random_letter(rng))
        }
    }
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(1721);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;
    let mut tries = 0usize;

    while count < target && tries < 100000 {
        tries += 1;
        let t: usize = match rng.gen_range_usize(0, 4) {
            0 => 1,
            1 => rng.gen_range_usize(2, 10),
            2 => rng.gen_range_usize(20, 50),
            3 => rng.gen_range_usize(50, 100),
            _ => rng.gen_range_usize(2, 30),
        };
        let mut cases: Vec<TC> = Vec::new();
        for _ in 0..t {
            let mode = (rng.next_u64() as usize) % 5;
            cases.push(gen_case(&mut rng, mode));
        }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let outs = build_output(&cases);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}

