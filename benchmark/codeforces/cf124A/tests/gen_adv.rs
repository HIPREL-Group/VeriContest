use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32, a: i32, b: i32) -> (result: (i32, i32, i32))
    requires
        1 <= n <= 100,
        0 <= a < n,
        0 <= b < n,
    ensures
        ({
            let (rn, ra, rb) = result;
            1 <= rn <= 100 && 0 <= ra < rn && 0 <= rb < rn
        }),
{
    (n, a, b)
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
    let target: usize = 200;
    let mut rng = Rng::new(987654321);
    let mut seen: HashSet<u64> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
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

    // Boundary corners
    for n in 1..=100i32 {
        emit(n, 0, 0, &mut seen, &mut out, &mut count);
        emit(n, n-1, n-1, &mut seen, &mut out, &mut count);
        emit(n, n/2, n/2, &mut seen, &mut out, &mut count);
        emit(n, 0, n-1, &mut seen, &mut out, &mut count);
        emit(n, n-1, 0, &mut seen, &mut out, &mut count);
    }

    let mut tries = 0;
    while count < target && tries < 10000 {
        tries += 1;
        let n = rng.gen_range_i32(1, 100);
        let a = rng.gen_range_i32(0, n - 1);
        let b = rng.gen_range_i32(0, n - 1);
        emit(n, a, b, &mut seen, &mut out, &mut count);
    }
}

