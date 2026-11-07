use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    seed_a: i32,
    seed_b: i32,
    seed_c: i32,
    mutation_kind: u8,
) -> (result: (i32, i32, i32))
    requires
        1 <= seed_a <= 100,
        1 <= seed_b <= 100,
        1 <= seed_c <= 10_000,
    ensures
        1 <= result.0 <= 100,
        1 <= result.1 <= 100,
        1 <= result.2 <= 10_000,
{
    if mutation_kind == 0 {
        // identity
        (seed_a, seed_b, seed_c)
    } else if mutation_kind == 1 {
        // nudge a up
        let a = if seed_a < 100 { (seed_a + 1) as i32 } else { seed_a };
        (a, seed_b, seed_c)
    } else if mutation_kind == 2 {
        // nudge a down
        let a = if seed_a > 1 { (seed_a - 1) as i32 } else { seed_a };
        (a, seed_b, seed_c)
    } else if mutation_kind == 3 {
        // nudge b up
        let b = if seed_b < 100 { (seed_b + 1) as i32 } else { seed_b };
        (seed_a, b, seed_c)
    } else if mutation_kind == 4 {
        // nudge b down
        let b = if seed_b > 1 { (seed_b - 1) as i32 } else { seed_b };
        (seed_a, b, seed_c)
    } else if mutation_kind == 5 {
        // nudge c up
        let c = if seed_c < 10_000 { (seed_c + 1) as i32 } else { seed_c };
        (seed_a, seed_b, c)
    } else if mutation_kind == 6 {
        // nudge c down
        let c = if seed_c > 1 { (seed_c - 1) as i32 } else { seed_c };
        (seed_a, seed_b, c)
    } else if mutation_kind == 7 {
        // boundary: a=1, b=1
        (1, 1, seed_c)
    } else if mutation_kind == 8 {
        // boundary: a=100, b=100
        (100, 100, seed_c)
    } else if mutation_kind == 9 {
        // boundary: c=1
        (seed_a, seed_b, 1)
    } else if mutation_kind == 10 {
        // boundary: c=10000
        (seed_a, seed_b, 10_000)
    } else if mutation_kind == 11 {
        // set a = b (equal guns)
        (seed_b, seed_b, seed_c)
    } else if mutation_kind == 12 {
        // set c = a (exactly one shot from Ebony)
        (seed_a, seed_b, seed_a)
    } else if mutation_kind == 13 {
        // set c = b (exactly one shot from Ivory)
        (seed_a, seed_b, seed_b)
    } else if mutation_kind == 14 {
        // halve a
        let a = if seed_a / 2 >= 1 { seed_a / 2 } else { 1i32 };
        (a, seed_b, seed_c)
    } else if mutation_kind == 15 {
        // double a (clamped)
        let a = if seed_a <= 50 { (seed_a * 2) as i32 } else { 100i32 };
        (a, seed_b, seed_c)
    } else if mutation_kind == 16 {
        // halve c
        let c = if seed_c / 2 >= 1 { seed_c / 2 } else { 1i32 };
        (seed_a, seed_b, c)
    } else {
        // fallback: identity
        (seed_a, seed_b, seed_c)
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
        lo + (self.next_u64() as i32).rem_euclid(hi - lo + 1)
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

fn build_input(a: i32, b: i32, c: i32) -> String { format!("{} {} {}\n", a, b, c) }
fn build_output(yes: bool) -> String { if yes { "Yes\n".into() } else { "No\n".into() } }

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(633);
    let mut seen: HashSet<(i32, i32, i32)> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |a: i32, b: i32, c: i32, seen: &mut HashSet<(i32, i32, i32)>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if a < 1 || a > 100 || b < 1 || b > 100 || c < 1 || c > 10_000 { return; }
        if !seen.insert((a, b, c)) { return; }
        let inp = build_input(a, b, c);
        let ans = Solution::exact_damage_possible(a, b, c);
        let outs = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    // Examples
    emit(4, 6, 15, &mut seen, &mut out, &mut count);
    emit(3, 2, 7, &mut seen, &mut out, &mut count);
    emit(6, 11, 6, &mut seen, &mut out, &mut count);

    // Edges
    emit(1, 1, 1, &mut seen, &mut out, &mut count);
    emit(1, 1, 10_000, &mut seen, &mut out, &mut count);
    emit(100, 100, 1, &mut seen, &mut out, &mut count);
    emit(100, 100, 100, &mut seen, &mut out, &mut count);
    emit(100, 100, 10_000, &mut seen, &mut out, &mut count);
    emit(2, 4, 7, &mut seen, &mut out, &mut count);
    emit(2, 3, 1, &mut seen, &mut out, &mut count);
    emit(50, 70, 100, &mut seen, &mut out, &mut count);

    while count < target {
        let a = rng.gen_range_i32(1, 100);
        let b = rng.gen_range_i32(1, 100);
        let c = rng.gen_range_i32(1, 10_000);
        emit(a, b, c, &mut seen, &mut out, &mut count);
    }
}

