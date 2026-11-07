use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i64, m: i64) -> (result: (i64, i64))
    requires
        0 <= n <= 500000,
        0 <= m <= 500000,
    ensures
        0 <= result.0 <= 500000,
        0 <= result.1 <= 500000,
{
    (n, m)
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
    let target_count: usize = 200;
    let mut rng = Rng::new(51904);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen: HashSet<String> = HashSet::new();
    let mut count = 0usize;

    let mut emit = |n: i64, m: i64, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count { return; }
        if n < 0 || n > 500_000 || m < 0 || m > 500_000 { return; }
        let key = format!("{}_{}", n, m);
        if !seen.insert(key) { return; }
        let result = Solution::max_training_teams(n, m);
        let inp = format!("{} {}\n", n, m);
        let outp = format!("{}\n", result);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    // Adversarial: boundaries, where each branch wins
    for x in [0i64, 1, 2, 3, 4, 5, 10, 100, 1000, 100_000, 250_000, 499_999, 500_000].iter() {
        emit(*x, 0, &mut seen, &mut out, &mut count);
        emit(0, *x, &mut seen, &mut out, &mut count);
        emit(*x, *x, &mut seen, &mut out, &mut count);
        emit(*x, 2 * *x, &mut seen, &mut out, &mut count);
        emit(2 * *x, *x, &mut seen, &mut out, &mut count);
        emit(*x, 3 * *x, &mut seen, &mut out, &mut count);
        emit(3 * *x, *x, &mut seen, &mut out, &mut count);
    }

    // Boundaries near 500_000
    for delta in 0..10 {
        emit(500_000 - delta, 500_000, &mut seen, &mut out, &mut count);
        emit(500_000, 500_000 - delta, &mut seen, &mut out, &mut count);
        emit(500_000 - delta, 500_000 - delta, &mut seen, &mut out, &mut count);
    }

    while count < target_count {
        let n = rng.gen_range_i64(0, 500_000);
        let m = rng.gen_range_i64(0, 500_000);
        emit(n, m, &mut seen, &mut out, &mut count);
    }
}

