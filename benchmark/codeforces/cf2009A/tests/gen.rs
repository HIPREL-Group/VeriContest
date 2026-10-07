use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_a: i32, seed_b: i32, mutation_kind: u8) -> (result: (i32, i32))
    requires
        1 <= seed_a <= seed_b <= 10,
    ensures
        1 <= result.0 <= result.1 <= 10,
{
    if mutation_kind == 0 {
        (seed_a, seed_b)
    } else if mutation_kind == 1 {
        (1i32, 1i32)
    } else if mutation_kind == 2 {
        (1i32, 10i32)
    } else if mutation_kind == 3 {
        (10i32, 10i32)
    } else if mutation_kind == 4 && seed_b < 10 {
        (seed_a, seed_b + 1)
    } else if mutation_kind == 5 && seed_a > 1 && seed_a - 1 <= seed_b {
        (seed_a - 1, seed_b)
    } else if mutation_kind == 6 {
        (seed_a, seed_a)
    } else if mutation_kind == 7 {
        (1i32, seed_b)
    } else if mutation_kind == 8 {
        (seed_a, 10i32)
    } else {
        (seed_a, seed_b)
    }
}

} // verus!

use std::io::Write;
use std::collections::HashSet;

struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0
    }
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let r = (hi as i64 - lo as i64 + 1) as u64;
        (lo as i64 + (self.next_u64() % r) as i64) as i32
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

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);
    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;
    let mut seen = HashSet::new();
    
    while count < target {
        let t = if count < 5 { 1usize } else { rng.gen_range_usize(1, 30) };
        let mut input = format!("{}\n", t);
        let mut output = String::new();
        for _ in 0..t {
            // Generate seed (a, b) satisfying preconditions
            let sa = rng.gen_range_i32(1, 10);
            let sb = rng.gen_range_i32(sa, 10);
            let mk = (rng.next_u64() % 10) as u8;
            let (a, b) = generate_test_case(sa, sb, mk);
            input.push_str(&format!("{} {}\n", a, b));
            let ans = Solution::minimize_value(a, b);
            output.push_str(&format!("{}\n", ans));
        }
        let key = input.clone();
        if !seen.insert(key) { continue; }
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&input), fmt_json_str(&output)).unwrap();
        count += 1;
    }
}
