use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    a_seed: i64,
    b_seed: i64,
    mutation_kind: u8,
) -> (result: (i64, i64))
    requires
        1 <= a_seed <= 100,
        1 <= b_seed <= 100,
    ensures
        1 <= result.0 <= 100,
        1 <= result.1 <= 100,
{
    if mutation_kind == 0 {
        // identity
        (a_seed, b_seed)
    } else if mutation_kind == 1 && a_seed < 100 {
        // nudge a up
        (a_seed + 1, b_seed)
    } else if mutation_kind == 2 && a_seed > 1 {
        // nudge a down
        (a_seed - 1, b_seed)
    } else if mutation_kind == 3 && b_seed < 100 {
        // nudge b up
        (a_seed, b_seed + 1)
    } else if mutation_kind == 4 && b_seed > 1 {
        // nudge b down
        (a_seed, b_seed - 1)
    } else if mutation_kind == 5 {
        // a = b (equal socks)
        (a_seed, a_seed)
    } else if mutation_kind == 6 {
        // swap a and b
        (b_seed, a_seed)
    } else if mutation_kind == 7 {
        // both at min boundary
        (1, 1)
    } else if mutation_kind == 8 {
        // both at max boundary
        (100, 100)
    } else if mutation_kind == 9 {
        // a at min, b as seed
        (1, b_seed)
    } else if mutation_kind == 10 {
        // a at max, b as seed
        (100, b_seed)
    } else if mutation_kind == 11 {
        // a as seed, b at min
        (a_seed, 1)
    } else if mutation_kind == 12 {
        // a as seed, b at max
        (a_seed, 100)
    } else if mutation_kind == 13 {
        // halve a
        let a2: i64 = if a_seed / 2 >= 1 { a_seed / 2 } else { 1 };
        (a2, b_seed)
    } else if mutation_kind == 14 {
        // halve b
        let b2: i64 = if b_seed / 2 >= 1 { b_seed / 2 } else { 1 };
        (a_seed, b2)
    } else if mutation_kind == 15 && a_seed <= 50 {
        // double a
        (a_seed * 2, b_seed)
    } else if mutation_kind == 16 && b_seed <= 50 {
        // double b
        (a_seed, b_seed * 2)
    } else {
        // fallback: identity
        (a_seed, b_seed)
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

fn build_input(a: i64, b: i64) -> String { format!("{} {}\n", a, b) }
fn build_output(x: i64, y: i64) -> String { format!("{} {}\n", x, y) }

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(581);
    let mut seen: HashSet<String> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |a: i64, b: i64, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if a < 1 || a > 100 || b < 1 || b > 100 { return; }
        let key = format!("{} {}", a, b);
        if !seen.insert(key) { return; }
        let inp = build_input(a, b);
        let (x, y) = Solution::hipster_sock_days(a, b);
        let outs = build_output(x, y);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    // Examples
    emit(3, 1, &mut seen, &mut out, &mut count);
    emit(2, 3, &mut seen, &mut out, &mut count);
    emit(7, 3, &mut seen, &mut out, &mut count);

    // Edges
    emit(1, 1, &mut seen, &mut out, &mut count);
    emit(100, 100, &mut seen, &mut out, &mut count);
    emit(1, 100, &mut seen, &mut out, &mut count);
    emit(100, 1, &mut seen, &mut out, &mut count);
    emit(1, 2, &mut seen, &mut out, &mut count);
    emit(2, 1, &mut seen, &mut out, &mut count);
    emit(2, 2, &mut seen, &mut out, &mut count);
    emit(50, 50, &mut seen, &mut out, &mut count);

    while count < target {
        let a = rng.gen_range_i64(1, 100);
        let b = rng.gen_range_i64(1, 100);
        emit(a, b, &mut seen, &mut out, &mut count);
    }
}

