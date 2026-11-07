use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: u32, mutation_kind: u8) -> (result: u32)
    requires
        1 <= seed <= 100,
    ensures
        1 <= result <= 100,
{
    if mutation_kind == 0 {
        seed                                          // identity
    } else if mutation_kind == 1 && seed < 100 {
        seed + 1                                      // nudge up
    } else if mutation_kind == 2 && seed > 1 {
        seed - 1                                      // nudge down
    } else if mutation_kind == 3 {
        if seed <= 50 {
            seed * 2                                  // double
        } else {
            seed
        }
    } else if mutation_kind == 4 {
        seed / 2 + 1                                  // halve (stay >= 1)
    } else if mutation_kind == 5 {
        1                                             // min boundary
    } else if mutation_kind == 6 {
        100                                           // max boundary
    } else if mutation_kind == 7 {
        50                                            // midpoint
    } else if mutation_kind == 8 {
        if seed <= 99 {
            101 - seed                                // mirror around 50.5
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
        self.0 = self.0.wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0
    }

    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        assert!(lo <= hi);
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
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
    let mut rng = Rng::new(4);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen: HashSet<u32> = HashSet::new();
    let mut count = 0usize;

    let mut emit = |w: u32, seen: &mut HashSet<u32>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count { return; }
        if w < 1 || w > 100 { return; }
        if !seen.insert(w) { return; }
        let result = Solution::can_split_even(w);
        let inp = format!("{}\n", w);
        let outp = if result { "YES\n".to_string() } else { "NO\n".to_string() };
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    emit(8, &mut seen, &mut out, &mut count);

    // All values 1..=100
    for w in 1..=100 {
        emit(w, &mut seen, &mut out, &mut count);
    }
}

