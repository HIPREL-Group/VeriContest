use vstd::prelude::*;

verus! {

pub fn generate_test_case(n_seed: i32, a_raw: i32, b_raw: i32, mutation_kind: u8) -> (result: (i32, i32, i32))
    requires
        1 <= n_seed <= 100,
        0 <= a_raw <= 99,
        0 <= b_raw <= 99,
    ensures
        1 <= result.0 <= 100,
        0 <= result.1 < result.0,
        0 <= result.2 < result.0,
{
    let n = n_seed;
    let a_clamped: i32 = if a_raw < n { a_raw } else { n - 1 };
    let b_clamped: i32 = if b_raw < n { b_raw } else { n - 1 };

    if mutation_kind == 0 {
        // identity
        (n, a_clamped, b_clamped)
    } else if mutation_kind == 1 && a_clamped > 0 {
        // nudge a down
        (n, a_clamped - 1, b_clamped)
    } else if mutation_kind == 2 && a_clamped < n - 1 {
        // nudge a up
        (n, a_clamped + 1, b_clamped)
    } else if mutation_kind == 3 && b_clamped > 0 {
        // nudge b down
        (n, a_clamped, b_clamped - 1)
    } else if mutation_kind == 4 && b_clamped < n - 1 {
        // nudge b up
        (n, a_clamped, b_clamped + 1)
    } else if mutation_kind == 5 {
        // a = 0
        (n, 0, b_clamped)
    } else if mutation_kind == 6 {
        // b = 0
        (n, a_clamped, 0)
    } else if mutation_kind == 7 {
        // a = n-1
        (n, n - 1, b_clamped)
    } else if mutation_kind == 8 {
        // b = n-1
        (n, a_clamped, n - 1)
    } else if mutation_kind == 9 {
        // a = 0, b = 0
        (n, 0, 0)
    } else if mutation_kind == 10 {
        // a = n-1, b = n-1
        (n, n - 1, n - 1)
    } else if mutation_kind == 11 && b_clamped < n {
        // swap a and b
        (n, b_clamped, a_clamped)
    } else {
        // fallback
        (n, a_clamped, b_clamped)
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
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let r = (hi as i64 - lo as i64 + 1) as u64;
        (lo as i64 + (self.next_u64() as u64 % r) as i64) as i32
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

fn build_input(n: i32, a: i32, b: i32) -> String {
    format!("{} {} {}\n", n, a, b)
}

fn build_output(ans: i32) -> String { format!("{}\n", ans) }

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let mut seen: HashSet<u64> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |n: i32, a: i32, b: i32, seen: &mut HashSet<u64>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if !(0 <= a && a < n && 0 <= b && b < n) { return; }
        let mut h: u64 = 1469598103934665603;
        h ^= n as u64; h = h.wrapping_mul(1099511628211);
        h ^= a as u64; h = h.wrapping_mul(1099511628211);
        h ^= b as u64; h = h.wrapping_mul(1099511628211);
        if !seen.insert(h) { return; }
        let inp = build_input(n, a, b);
        let ans = Solution::count_positions(n, a, b);
        let outs = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    // Examples
    emit(3, 1, 1, &mut seen, &mut out, &mut count);
    emit(5, 2, 3, &mut seen, &mut out, &mut count);

    // Edge cases
    emit(1, 0, 0, &mut seen, &mut out, &mut count);
    emit(2, 0, 0, &mut seen, &mut out, &mut count);
    emit(2, 1, 1, &mut seen, &mut out, &mut count);
    emit(100, 0, 0, &mut seen, &mut out, &mut count);
    emit(100, 99, 99, &mut seen, &mut out, &mut count);
    emit(100, 50, 50, &mut seen, &mut out, &mut count);

    while count < target {
        let n = rng.gen_range_i32(1, 100);
        let a = rng.gen_range_i32(0, n - 1);
        let b = rng.gen_range_i32(0, n - 1);
        emit(n, a, b, &mut seen, &mut out, &mut count);
    }
}

