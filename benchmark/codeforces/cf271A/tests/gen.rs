use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: i32, mutation_kind: u8) -> (result: i32)
    requires
        1000 <= seed <= 9000,
    ensures
        1000 <= result <= 9000,
{
    if mutation_kind == 0 {
        seed
    } else if mutation_kind == 1 && seed < 9000 {
        (seed + 1) as i32
    } else if mutation_kind == 2 && seed > 1000 {
        (seed - 1) as i32
    } else if mutation_kind == 3 {
        let mirrored = (10000 - seed) as i32;
        if mirrored >= 1000 && mirrored <= 9000 {
            mirrored
        } else {
            seed
        }
    } else if mutation_kind == 4 {
        1000
    } else if mutation_kind == 5 {
        9000
    } else if mutation_kind == 6 {
        5000
    } else if mutation_kind == 7 {
        let half = seed / 2;
        if half >= 1000 {
            half
        } else {
            seed
        }
    } else if mutation_kind == 8 {
        let dbl = if seed <= 4500 { seed * 2 } else { 9000i32 };
        if dbl >= 1000 && dbl <= 9000 {
            dbl
        } else {
            seed
        }
    } else {
        seed
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

fn build_input(y: i32) -> String {
    format!("{}\n", y)
}

fn build_output(ans: i32) -> String {
    format!("{}\n", ans)
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(271);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    // Examples + key boundary tests
    let key_inputs: Vec<i32> = vec![1987, 2013, 1000, 9000, 1234, 8999, 1023];
    for &y in &key_inputs {
        if count >= target { break; }
        let inp = build_input(y);
        if !seen.insert(inp.clone()) { continue; }
        let ans = Solution::beautiful_year(y);
        let outp = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }

    let mut tries = 0;
    while count < target && tries < target * 100 {
        tries += 1;
        let y = rng.gen_range_i64(1000, 9000) as i32;
        let inp = build_input(y);
        if !seen.insert(inp.clone()) { continue; }
        let ans = Solution::beautiful_year(y);
        let outp = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

