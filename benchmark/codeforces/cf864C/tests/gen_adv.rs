use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    a_val: i64,
    b_val: i64,
    f_val: i64,
    k_val: usize,
) -> (r: (i64, i64, i64, usize))
    requires
        0 < f_val < a_val <= 1_000_000,
        1 <= b_val <= 1_000_000_000,
        1 <= k_val <= 10_000,
    ensures
        ({
            let (a, b, f, k) = r;
            &&& 0 < f < a <= 1_000_000
            &&& 1 <= b <= 1_000_000_000
            &&& 1 <= k <= 10_000
            &&& a == a_val
            &&& b == b_val
            &&& f == f_val
            &&& k == k_val
        }),
{
    (a_val, b_val, f_val, k_val)
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
    let target: usize = 200;
    let mut rng = Rng::new(86401);
    let mut seen: HashSet<(i64, i64, i64, usize)> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
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

    // Boundary
    emit(2, 1, 1, 1, &mut seen, &mut out, &mut count);
    emit(2, 1, 1, 10_000, &mut seen, &mut out, &mut count);
    emit(1_000_000, 1, 500_000, 1, &mut seen, &mut out, &mut count);
    emit(1_000_000, 1_000_000_000, 500_000, 10_000, &mut seen, &mut out, &mut count);
    emit(1_000_000, 999_999, 1, 1, &mut seen, &mut out, &mut count);
    emit(1_000_000, 1_000_000, 1, 1, &mut seen, &mut out, &mut count);

    // Various k & b
    for k in [1usize, 2, 10, 100, 1000, 10_000] {
        emit(10, 5, 5, k, &mut seen, &mut out, &mut count);
        emit(10, 9, 5, k, &mut seen, &mut out, &mut count);
        emit(10, 10, 5, k, &mut seen, &mut out, &mut count);
        emit(10, 20, 5, k, &mut seen, &mut out, &mut count);
        emit(100, 50, 50, k, &mut seen, &mut out, &mut count);
    }

    while count < target {
        let a = rng.gen_range_i64(2, 100);
        let f = rng.gen_range_i64(1, a - 1);
        let b = rng.gen_range_i64(1, 200);
        let k = rng.gen_range_usize(1, 100);
        emit(a, b, f, k, &mut seen, &mut out, &mut count);
    }
}

