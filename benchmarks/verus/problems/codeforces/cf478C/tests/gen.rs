use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    seed_r: i64,
    seed_g: i64,
    seed_b: i64,
    mutation_kind: u8,
) -> (result: (i64, i64, i64))
    requires
        0 <= seed_r <= 2_000_000_000i64,
        0 <= seed_g <= 2_000_000_000i64,
        0 <= seed_b <= 2_000_000_000i64,
    ensures
        0 <= result.0 <= 2_000_000_000i64,
        0 <= result.1 <= 2_000_000_000i64,
        0 <= result.2 <= 2_000_000_000i64,
{
    if mutation_kind == 0 {
        // identity
        (seed_r, seed_g, seed_b)
    } else if mutation_kind == 1 && seed_r < 2_000_000_000 {
        // nudge r up
        (seed_r + 1, seed_g, seed_b)
    } else if mutation_kind == 2 && seed_r > 0 {
        // nudge r down
        (seed_r - 1, seed_g, seed_b)
    } else if mutation_kind == 3 && seed_g < 2_000_000_000 {
        // nudge g up
        (seed_r, seed_g + 1, seed_b)
    } else if mutation_kind == 4 && seed_b < 2_000_000_000 {
        // nudge b up
        (seed_r, seed_g, seed_b + 1)
    } else if mutation_kind == 5 {
        // halve r
        (seed_r / 2, seed_g, seed_b)
    } else if mutation_kind == 6 {
        // double r (if in range)
        if seed_r <= 1_000_000_000 {
            (seed_r * 2, seed_g, seed_b)
        } else {
            (seed_r, seed_g, seed_b)
        }
    } else if mutation_kind == 7 {
        // zero out r
        (0, seed_g, seed_b)
    } else if mutation_kind == 8 {
        // max boundary r
        (2_000_000_000, seed_g, seed_b)
    } else if mutation_kind == 9 {
        // all zero
        (0, 0, 0)
    } else if mutation_kind == 10 {
        // all max
        (2_000_000_000, 2_000_000_000, 2_000_000_000)
    } else if mutation_kind == 11 {
        // all same
        (seed_r, seed_r, seed_r)
    } else if mutation_kind == 12 {
        // one dominant: r max, others zero
        (2_000_000_000, 0, 0)
    } else if mutation_kind == 13 {
        // swap r and g
        (seed_g, seed_r, seed_b)
    } else if mutation_kind == 14 {
        // swap r and b
        (seed_b, seed_g, seed_r)
    } else {
        // fallback: identity
        (seed_r, seed_g, seed_b)
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
    let mut rng = Rng::new(478);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen: HashSet<String> = HashSet::new();
    let mut count = 0usize;

    let mut emit = |r: i64, g: i64, b: i64, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count { return; }
        if r < 0 || g < 0 || b < 0 || r > 2_000_000_000 || g > 2_000_000_000 || b > 2_000_000_000 { return; }
        let key = format!("{}_{}_{}", r, g, b);
        if !seen.insert(key) { return; }
        let result = Solution::max_decorated_tables(r, g, b);
        let inp = format!("{} {} {}\n", r, g, b);
        let outp = format!("{}\n", result);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    emit(5, 4, 3, &mut seen, &mut out, &mut count);
    emit(1, 1, 1, &mut seen, &mut out, &mut count);
    emit(2, 3, 3, &mut seen, &mut out, &mut count);

    emit(0, 0, 0, &mut seen, &mut out, &mut count);
    emit(0, 0, 1, &mut seen, &mut out, &mut count);
    emit(0, 1, 1, &mut seen, &mut out, &mut count);
    emit(0, 2, 2, &mut seen, &mut out, &mut count);
    emit(0, 5, 5, &mut seen, &mut out, &mut count);
    emit(0, 0, 100, &mut seen, &mut out, &mut count);
    emit(2_000_000_000, 2_000_000_000, 2_000_000_000, &mut seen, &mut out, &mut count);
    emit(2_000_000_000, 0, 0, &mut seen, &mut out, &mut count);
    emit(2_000_000_000, 1, 0, &mut seen, &mut out, &mut count);
    emit(2_000_000_000, 1, 1, &mut seen, &mut out, &mut count);
    emit(1, 1, 2_000_000_000, &mut seen, &mut out, &mut count);
    emit(1_000_000_000, 1_000_000_000, 1_000_000_000, &mut seen, &mut out, &mut count);
    emit(2, 2, 2, &mut seen, &mut out, &mut count);
    emit(3, 3, 3, &mut seen, &mut out, &mut count);
    emit(10, 1, 1, &mut seen, &mut out, &mut count);

    while count < target_count {
        let r = rng.gen_range_i64(0, 2_000_000_000);
        let g = rng.gen_range_i64(0, 2_000_000_000);
        let b = rng.gen_range_i64(0, 2_000_000_000);
        emit(r, g, b, &mut seen, &mut out, &mut count);
    }
}

