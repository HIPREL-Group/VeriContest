use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: u32, mutation_kind: u8) -> (result: u32)
    requires
        1 <= seed <= 500,
    ensures
        1 <= result <= 500,
{
    if mutation_kind == 0 {
        seed
    } else if mutation_kind == 1 && seed < 500 {
        seed + 1
    } else if mutation_kind == 2 && seed > 1 {
        seed - 1
    } else if mutation_kind == 3 {
        if seed <= 250 { seed * 2 } else { seed }
    } else if mutation_kind == 4 {
        seed / 2 + 1
    } else if mutation_kind == 5 {
        1
    } else if mutation_kind == 6 {
        500
    } else if mutation_kind == 7 {
        250
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
    fn gen_range_u32(&mut self, lo: u32, hi: u32) -> u32 {
        lo + (self.next_u64() as u32) % (hi - lo + 1)
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
    let target_count: usize = 100;
    let mut rng = Rng::new(47);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen: HashSet<u32> = HashSet::new();
    let mut count = 0usize;

    let mut emit = |n: u32, seen: &mut HashSet<u32>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count { return; }
        if n < 1 || n > 500 { return; }
        if !seen.insert(n) { return; }
        let result = Solution::is_triangular(n);
        let inp = format!("{}\n", n);
        let outp = if result { "YES\n".to_string() } else { "NO\n".to_string() };
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    // All triangular numbers <= 500
    for k in 1u32..32 {
        emit(k * (k + 1) / 2, &mut seen, &mut out, &mut count);
    }
    // Some specific values
    for n in 1u32..=80 {
        emit(n, &mut seen, &mut out, &mut count);
    }
    while count < target_count {
        let seed = rng.gen_range_u32(1, 500);
        let kind = (rng.next_u64() % 9) as u8;
        let v = generate_test_case(seed, kind);
        emit(v, &mut seen, &mut out, &mut count);
    }
}
