use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    seed_a1: i32,
    seed_b1: i32,
    seed_a2: i32,
    seed_b2: i32,
    seed_a3: i32,
    seed_b3: i32,
    mutation_kind: u8,
) -> (result: (i32, i32, i32, i32, i32, i32))
    requires
        1 <= seed_a1 <= 1000,
        1 <= seed_b1 <= 1000,
        1 <= seed_a2 <= 1000,
        1 <= seed_b2 <= 1000,
        1 <= seed_a3 <= 1000,
        1 <= seed_b3 <= 1000,
    ensures
        1 <= result.0 <= 1000,
        1 <= result.1 <= 1000,
        1 <= result.2 <= 1000,
        1 <= result.3 <= 1000,
        1 <= result.4 <= 1000,
        1 <= result.5 <= 1000,
{
    if mutation_kind == 0 {
        // identity
        (seed_a1, seed_b1, seed_a2, seed_b2, seed_a3, seed_b3)
    } else if mutation_kind == 1 {
        // nudge a1 up
        let a1 = if seed_a1 < 1000 { (seed_a1 + 1) as i32 } else { seed_a1 };
        (a1, seed_b1, seed_a2, seed_b2, seed_a3, seed_b3)
    } else if mutation_kind == 2 {
        // nudge a1 down
        let a1 = if seed_a1 > 1 { (seed_a1 - 1) as i32 } else { seed_a1 };
        (a1, seed_b1, seed_a2, seed_b2, seed_a3, seed_b3)
    } else if mutation_kind == 3 {
        // all min boundary
        (1, 1, 1, 1, 1, 1)
    } else if mutation_kind == 4 {
        // all max boundary
        (1000, 1000, 1000, 1000, 1000, 1000)
    } else if mutation_kind == 5 {
        // swap a2/b2 dimensions (rotate painting 2)
        (seed_a1, seed_b1, seed_b2, seed_a2, seed_a3, seed_b3)
    } else if mutation_kind == 6 {
        // swap a3/b3 dimensions (rotate painting 3)
        (seed_a1, seed_b1, seed_a2, seed_b2, seed_b3, seed_a3)
    } else if mutation_kind == 7 {
        // swap board dimensions
        (seed_b1, seed_a1, seed_a2, seed_b2, seed_a3, seed_b3)
    } else if mutation_kind == 8 {
        // halve all values (clamped to 1)
        let a1 = if seed_a1 / 2 >= 1 { seed_a1 / 2 } else { 1i32 };
        let b1 = if seed_b1 / 2 >= 1 { seed_b1 / 2 } else { 1i32 };
        let a2 = if seed_a2 / 2 >= 1 { seed_a2 / 2 } else { 1i32 };
        let b2 = if seed_b2 / 2 >= 1 { seed_b2 / 2 } else { 1i32 };
        let a3 = if seed_a3 / 2 >= 1 { seed_a3 / 2 } else { 1i32 };
        let b3 = if seed_b3 / 2 >= 1 { seed_b3 / 2 } else { 1i32 };
        (a1, b1, a2, b2, a3, b3)
    } else if mutation_kind == 9 {
        // double all values (clamped to 1000)
        let a1 = if seed_a1 * 2 <= 1000 { seed_a1 * 2 } else { 1000i32 };
        let b1 = if seed_b1 * 2 <= 1000 { seed_b1 * 2 } else { 1000i32 };
        let a2 = if seed_a2 * 2 <= 1000 { seed_a2 * 2 } else { 1000i32 };
        let b2 = if seed_b2 * 2 <= 1000 { seed_b2 * 2 } else { 1000i32 };
        let a3 = if seed_a3 * 2 <= 1000 { seed_a3 * 2 } else { 1000i32 };
        let b3 = if seed_b3 * 2 <= 1000 { seed_b3 * 2 } else { 1000i32 };
        (a1, b1, a2, b2, a3, b3)
    } else if mutation_kind == 10 {
        // make paintings small relative to board: set paintings to 1
        (seed_a1, seed_b1, 1, 1, 1, 1)
    } else if mutation_kind == 11 {
        // make paintings same size as board
        (seed_a1, seed_b1, seed_a1, seed_b1, seed_a1, seed_b1)
    } else {
        // fallback: identity
        (seed_a1, seed_b1, seed_a2, seed_b2, seed_a3, seed_b3)
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
    let mut rng = Rng::new(560);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen: HashSet<String> = HashSet::new();
    let mut count = 0usize;

    let mut emit = |a1: i32, b1: i32, a2: i32, b2: i32, a3: i32, b3: i32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count { return; }
        for v in [a1, b1, a2, b2, a3, b3].iter() {
            if *v < 1 || *v > 1000 { return; }
        }
        let key = format!("{}_{}_{}_{}_{}_{}", a1, b1, a2, b2, a3, b3);
        if !seen.insert(key) { return; }
        let result = Solution::can_place_paintings(a1, b1, a2, b2, a3, b3);
        let inp = format!("{} {}\n{} {}\n{} {}\n", a1, b1, a2, b2, a3, b3);
        let outp = if result { "YES\n".to_string() } else { "NO\n".to_string() };
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    emit(3, 2, 1, 3, 2, 1, &mut seen, &mut out, &mut count);
    emit(5, 5, 3, 3, 3, 3, &mut seen, &mut out, &mut count);
    emit(4, 2, 2, 3, 1, 2, &mut seen, &mut out, &mut count);

    // Edge
    emit(1, 1, 1, 1, 1, 1, &mut seen, &mut out, &mut count);
    emit(1000, 1000, 1, 1, 1, 1, &mut seen, &mut out, &mut count);
    emit(1, 1000, 1000, 1, 1000, 1, &mut seen, &mut out, &mut count);
    emit(1, 2, 1, 1, 1, 1, &mut seen, &mut out, &mut count);
    emit(1, 1, 1, 2, 1, 1, &mut seen, &mut out, &mut count);
    emit(1000, 1000, 500, 1000, 500, 1000, &mut seen, &mut out, &mut count);
    emit(1000, 1000, 501, 1000, 500, 1000, &mut seen, &mut out, &mut count);

    while count < target_count {
        let a1 = rng.gen_range_i64(1, 1000) as i32;
        let b1 = rng.gen_range_i64(1, 1000) as i32;
        let a2 = rng.gen_range_i64(1, 1000) as i32;
        let b2 = rng.gen_range_i64(1, 1000) as i32;
        let a3 = rng.gen_range_i64(1, 1000) as i32;
        let b3 = rng.gen_range_i64(1, 1000) as i32;
        emit(a1, b1, a2, b2, a3, b3, &mut seen, &mut out, &mut count);
    }
}

