use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    seed_a: i64,
    seed_b: i64,
    seed_f: i64,
    seed_k: usize,
    mutation_kind: u8,
) -> (result: (i64, i64, i64, usize))
    requires
        2 <= seed_a <= 1_000_000,
        1 <= seed_b <= 1_000_000_000,
        1 <= seed_f <= seed_a - 1,
        1 <= seed_k <= 10_000,
    ensures
        0 < result.2 < result.0 <= 1_000_000,
        1 <= result.1 <= 1_000_000_000,
        1 <= result.3 <= 10_000,
{
    let a = seed_a;
    let b = seed_b;
    let f = seed_f;
    let k = seed_k;

    if mutation_kind == 0 {
        // identity
        (a, b, f, k)
    } else if mutation_kind == 1 {
        // min a: a = 2, f = 1
        (2i64, b, 1i64, k)
    } else if mutation_kind == 2 {
        // max a boundary
        (1_000_000i64, b, f, k)
    } else if mutation_kind == 3 {
        // min b
        (a, 1i64, f, k)
    } else if mutation_kind == 4 {
        // max b
        (a, 1_000_000_000i64, f, k)
    } else if mutation_kind == 5 {
        // min k
        (a, b, f, 1usize)
    } else if mutation_kind == 6 {
        // max k
        (a, b, f, 10_000usize)
    } else if mutation_kind == 7 {
        // f = 1 (gas station near start)
        (a, b, 1i64, k)
    } else if mutation_kind == 8 && a >= 3 {
        // f = a - 1 (gas station near end)
        (a, b, a - 1, k)
    } else if mutation_kind == 9 {
        // b = a (tank exactly covers one journey)
        if a <= 1_000_000_000 {
            (a, a, f, k)
        } else {
            (a, b, f, k)
        }
    } else if mutation_kind == 10 && a >= 4 {
        // f = a / 2 (gas station in middle)
        let mid = a / 2;
        // a >= 4, so mid >= 2, and mid <= a/2 < a
        assert(mid >= 1);
        assert(mid < a);
        (a, b, mid, k)
    } else if mutation_kind == 11 {
        // all minimums
        (2i64, 1i64, 1i64, 1usize)
    } else if mutation_kind == 12 {
        // all maximums
        (1_000_000i64, 1_000_000_000i64, 999_999i64, 10_000usize)
    } else {
        // fallback: identity
        (a, b, f, k)
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

fn build_input(a: i64, b: i64, f: i64, k: usize) -> String { format!("{} {} {} {}\n", a, b, f, k) }
fn build_output(ans: i64) -> String { format!("{}\n", ans) }

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(864);
    let mut seen: HashSet<(i64, i64, i64, usize)> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |a: i64, b: i64, f: i64, k: usize, seen: &mut HashSet<(i64, i64, i64, usize)>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if !(0 < f && f < a && a <= 1_000_000) { return; }
        if !(1 <= b && b <= 1_000_000_000) { return; }
        if !(1 <= k && k <= 10_000) { return; }
        if !seen.insert((a, b, f, k)) { return; }
        let inp = build_input(a, b, f, k);
        let ans = Solution::min_bus_refuels(a, b, f, k);
        let outs = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    // Examples
    emit(6, 9, 2, 4, &mut seen, &mut out, &mut count);
    emit(6, 10, 2, 4, &mut seen, &mut out, &mut count);
    emit(6, 5, 4, 3, &mut seen, &mut out, &mut count);

    // Edges
    emit(2, 1, 1, 1, &mut seen, &mut out, &mut count);
    emit(2, 1_000_000_000, 1, 1, &mut seen, &mut out, &mut count);
    emit(1_000_000, 1_000_000_000, 500_000, 1, &mut seen, &mut out, &mut count);
    emit(1_000_000, 1_000_000_000, 500_000, 10_000, &mut seen, &mut out, &mut count);
    emit(2, 1, 1, 10_000, &mut seen, &mut out, &mut count);

    while count < target {
        let a = rng.gen_range_i64(2, 1000);
        let f = rng.gen_range_i64(1, a - 1);
        let b = rng.gen_range_i64(1, 10_000);
        let k = rng.gen_range_usize(1, 100);
        emit(a, b, f, k, &mut seen, &mut out, &mut count);
    }
}

