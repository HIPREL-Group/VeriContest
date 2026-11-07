use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    seed_x1: i32,
    seed_x2: i32,
    seed_x3: i32,
    mutation_kind: u8,
) -> (result: (i32, i32, i32))
    requires
        1 <= seed_x1 as int <= 100,
        1 <= seed_x2 as int <= 100,
        1 <= seed_x3 as int <= 100,
        seed_x1 as int != seed_x2 as int,
        seed_x1 as int != seed_x3 as int,
        seed_x2 as int != seed_x3 as int,
    ensures
        1 <= result.0 as int <= 100,
        1 <= result.1 as int <= 100,
        1 <= result.2 as int <= 100,
        result.0 as int != result.1 as int,
        result.0 as int != result.2 as int,
        result.1 as int != result.2 as int,
{
    if mutation_kind == 0 {
        // identity
        (seed_x1, seed_x2, seed_x3)
    } else if mutation_kind == 1 && seed_x1 < 100
        && seed_x1 + 1 != seed_x2 && seed_x1 + 1 != seed_x3 {
        // nudge x1 up
        (seed_x1 + 1, seed_x2, seed_x3)
    } else if mutation_kind == 2 && seed_x1 > 1
        && seed_x1 - 1 != seed_x2 && seed_x1 - 1 != seed_x3 {
        // nudge x1 down
        (seed_x1 - 1, seed_x2, seed_x3)
    } else if mutation_kind == 3 && seed_x2 < 100
        && seed_x2 + 1 != seed_x1 && seed_x2 + 1 != seed_x3 {
        // nudge x2 up
        (seed_x1, seed_x2 + 1, seed_x3)
    } else if mutation_kind == 4 && seed_x3 < 100
        && seed_x3 + 1 != seed_x1 && seed_x3 + 1 != seed_x2 {
        // nudge x3 up
        (seed_x1, seed_x2, seed_x3 + 1)
    } else if mutation_kind == 5 {
        // swap x1 and x2
        (seed_x2, seed_x1, seed_x3)
    } else if mutation_kind == 6 {
        // swap x1 and x3
        (seed_x3, seed_x2, seed_x1)
    } else if mutation_kind == 7 {
        // rotate: (x2, x3, x1)
        (seed_x2, seed_x3, seed_x1)
    } else if mutation_kind == 8 {
        // halve x1 (floor), ensure distinct
        let h = seed_x1 / 2;
        let v = if h < 1 { 1i32 } else { h };
        if v != seed_x2 && v != seed_x3 {
            (v, seed_x2, seed_x3)
        } else {
            (seed_x1, seed_x2, seed_x3)
        }
    } else if mutation_kind == 9 {
        // boundary: set x1=1 if distinct
        if 1 != seed_x2 && 1 != seed_x3 {
            (1, seed_x2, seed_x3)
        } else {
            (seed_x1, seed_x2, seed_x3)
        }
    } else if mutation_kind == 10 {
        // boundary: set x1=100 if distinct
        if 100 != seed_x2 && 100 != seed_x3 {
            (100, seed_x2, seed_x3)
        } else {
            (seed_x1, seed_x2, seed_x3)
        }
    } else if mutation_kind == 11 {
        // boundary triple: 1, 50, 100
        (1, 50, 100)
    } else if mutation_kind == 12 {
        // boundary triple: 1, 2, 100
        (1, 2, 100)
    } else {
        // fallback
        (seed_x1, seed_x2, seed_x3)
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
fn build_output(ans: i32) -> String { format!("{}\n", ans) }

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(723);
    let mut seen: HashSet<(i32, i32, i32)> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |a: i32, b: i32, c: i32, seen: &mut HashSet<(i32, i32, i32)>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if a < 1 || a > 100 || b < 1 || b > 100 || c < 1 || c > 100 { return; }
        if a == b || a == c || b == c { return; }
        if !seen.insert((a, b, c)) { return; }
        let inp = build_input(a, b, c);
        let ans = Solution::min_total_meeting_distance(a, b, c);
        let outs = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    // Examples
    emit(7, 1, 4, &mut seen, &mut out, &mut count);
    emit(30, 20, 10, &mut seen, &mut out, &mut count);

    // Edges
    emit(1, 2, 3, &mut seen, &mut out, &mut count);
    emit(1, 50, 100, &mut seen, &mut out, &mut count);
    emit(1, 99, 100, &mut seen, &mut out, &mut count);
    emit(98, 99, 100, &mut seen, &mut out, &mut count);
    emit(50, 51, 52, &mut seen, &mut out, &mut count);

    while count < target {
        let a = rng.gen_range_i32(1, 100);
        let b = rng.gen_range_i32(1, 100);
        let c = rng.gen_range_i32(1, 100);
        emit(a, b, c, &mut seen, &mut out, &mut count);
    }
}

