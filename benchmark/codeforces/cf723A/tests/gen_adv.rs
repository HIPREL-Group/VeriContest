use vstd::prelude::*;

verus! {

pub fn generate_test_case(x1: i32, x2: i32, x3: i32) -> (res: (i32, i32, i32))
    requires
        1 <= x1 <= 100,
        1 <= x2 <= 100,
        1 <= x3 <= 100,
        x1 != x2,
        x1 != x3,
        x2 != x3,
    ensures
        ({
            let (a, b, c) = res;
            &&& 1 <= a as int <= 100
            &&& 1 <= b as int <= 100
            &&& 1 <= c as int <= 100
            &&& a as int != b as int
            &&& a as int != c as int
            &&& b as int != c as int
        }),
{
    (x1, x2, x3)
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
    let target: usize = 200;
    let mut rng = Rng::new(72301);
    let mut seen: HashSet<(i32, i32, i32)> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
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

    // Boundaries
    emit(1, 2, 100, &mut seen, &mut out, &mut count);
    emit(1, 50, 100, &mut seen, &mut out, &mut count);
    emit(1, 99, 100, &mut seen, &mut out, &mut count);
    emit(2, 3, 4, &mut seen, &mut out, &mut count);

    // Adjacent triples
    for k in 1..=98i32 {
        emit(k, k + 1, k + 2, &mut seen, &mut out, &mut count);
    }

    // All permutations of (1, m, 100)
    for m in 2..=99i32 {
        emit(1, m, 100, &mut seen, &mut out, &mut count);
        emit(100, m, 1, &mut seen, &mut out, &mut count);
        emit(m, 1, 100, &mut seen, &mut out, &mut count);
        emit(m, 100, 1, &mut seen, &mut out, &mut count);
        if count >= target { break; }
    }

    while count < target {
        let a = rng.gen_range_i32(1, 100);
        let b = rng.gen_range_i32(1, 100);
        let c = rng.gen_range_i32(1, 100);
        emit(a, b, c, &mut seen, &mut out, &mut count);
    }
}

