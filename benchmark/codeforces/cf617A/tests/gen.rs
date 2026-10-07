use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: u64, mutation_kind: u8) -> (result: u64)
    requires
        1 <= seed <= 1_000_000,
    ensures
        1 <= result <= 1_000_000,
{
    if mutation_kind == 0 {
        seed                                          // identity
    } else if mutation_kind == 1 && seed < 1_000_000 {
        seed + 1                                      // nudge up
    } else if mutation_kind == 2 && seed > 1 {
        seed - 1                                      // nudge down
    } else if mutation_kind == 3 {
        if seed <= 500_000 {
            seed * 2                                  // double
        } else {
            seed
        }
    } else if mutation_kind == 4 {
        if seed >= 2 {
            seed / 2                                  // halve (min 1 since seed >= 2 => seed/2 >= 1)
        } else {
            seed
        }
    } else if mutation_kind == 5 {
        1                                             // min boundary
    } else if mutation_kind == 6 {
        1_000_000                                     // max boundary
    } else if mutation_kind == 7 {
        5                                             // exact multiple of 5
    } else if mutation_kind == 8 {
        if seed <= 999_996 {
            let rem = seed % 5;
            seed + (5 - rem) % 5                      // round up to next multiple of 5
        } else {
            seed
        }
    } else if mutation_kind == 9 {
        let rem = seed % 5;
        if rem > 0 && seed > 5 {
            seed - rem                                // round down to multiple of 5 (>= 5 since seed > 5)
        } else {
            seed
        }
    } else {
        seed                                          // fallback
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
    fn gen_range_u64(&mut self, lo: u64, hi: u64) -> u64 {
        lo + self.next_u64() % (hi - lo + 1)
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

fn build_input(x: u64) -> String { format!("{}\n", x) }
fn build_output(ans: u64) -> String { format!("{}\n", ans) }

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(617);
    let mut seen: HashSet<u64> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |x: u64, seen: &mut HashSet<u64>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if x < 1 || x > 1_000_000 { return; }
        if !seen.insert(x) { return; }
        let inp = build_input(x);
        let ans = Solution::min_steps(x);
        let outs = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    // Examples
    emit(5, &mut seen, &mut out, &mut count);
    emit(12, &mut seen, &mut out, &mut count);

    // Edges
    emit(1, &mut seen, &mut out, &mut count);
    emit(2, &mut seen, &mut out, &mut count);
    emit(3, &mut seen, &mut out, &mut count);
    emit(4, &mut seen, &mut out, &mut count);
    emit(5, &mut seen, &mut out, &mut count);
    emit(6, &mut seen, &mut out, &mut count);
    emit(10, &mut seen, &mut out, &mut count);
    emit(1_000_000, &mut seen, &mut out, &mut count);
    emit(999_999, &mut seen, &mut out, &mut count);

    // Boundaries near multiples of 5
    for k in 1..=20u64 {
        emit(5 * k - 1, &mut seen, &mut out, &mut count);
        emit(5 * k, &mut seen, &mut out, &mut count);
        emit(5 * k + 1, &mut seen, &mut out, &mut count);
    }

    while count < target {
        let x = rng.gen_range_u64(1, 1_000_000);
        emit(x, &mut seen, &mut out, &mut count);
    }
}

