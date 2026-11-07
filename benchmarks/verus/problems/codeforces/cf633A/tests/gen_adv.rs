use vstd::prelude::*;

verus! {

pub fn generate_test_case(a: i32, b: i32, c: i32) -> (res: (i32, i32, i32))
    requires
        1 <= a <= 100,
        1 <= b <= 100,
        1 <= c <= 10_000,
    ensures
        1 <= res.0 <= 100,
        1 <= res.1 <= 100,
        1 <= res.2 <= 10_000,
{
    (a, b, c)
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
    let target: usize = 200;
    let mut rng = Rng::new(63301);
    let mut seen: HashSet<(i32, i32, i32)> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
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

    // Boundaries
    for &a in &[1, 2, 3, 50, 99, 100i32] {
        for &b in &[1, 2, 3, 50, 99, 100i32] {
            for &c in &[1, 2, 7, 100, 9999, 10000i32] {
                emit(a, b, c, &mut seen, &mut out, &mut count);
            }
        }
    }

    // a == b
    for v in 1..=20i32 {
        for c in [1, v, v + 1, 2 * v, 3 * v, 100, 10_000] {
            emit(v, v, c, &mut seen, &mut out, &mut count);
            if count >= target { break; }
        }
    }

    while count < target {
        let a = rng.gen_range_i32(1, 100);
        let b = rng.gen_range_i32(1, 100);
        let c = rng.gen_range_i32(1, 10_000);
        emit(a, b, c, &mut seen, &mut out, &mut count);
    }
}

