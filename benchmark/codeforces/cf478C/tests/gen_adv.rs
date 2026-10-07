use vstd::prelude::*;

verus! {

pub fn generate_test_case(r: i64, g: i64, b: i64) -> (result: (i64, i64, i64))
    requires
        0 <= r <= 2_000_000_000,
        0 <= g <= 2_000_000_000,
        0 <= b <= 2_000_000_000,
    ensures
        ({
            let (rr, gg, bb) = result;
            &&& 0 <= rr <= 2_000_000_000
            &&& 0 <= gg <= 2_000_000_000
            &&& 0 <= bb <= 2_000_000_000
        }),
{
    (r, g, b)
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
    let mut rng = Rng::new(47802);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen: HashSet<String> = HashSet::new();
    let mut count = 0usize;

    let mut emit = |r: i64, g: i64, b: i64, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count { return; }
        if r < 0 || g < 0 || b < 0 || r > 2_000_000_000 || g > 2_000_000_000 || b > 2_000_000_000 { return; }
        let key = format!("{}_{}_{}", r, g, b);
        if !seen.insert(key) { return; }
        let result = Solution::max_decorated_tables(r, g, b);
        let inp = format!("{} {} {}\n", r, g, b);
        let outp = format!("{}\n", result);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    // Adversarial: extreme dominance and equal cases
    for x in [0i64, 1, 2, 3, 5, 10, 100, 1_000_000, 10_000_000, 1_000_000_000, 2_000_000_000].iter() {
        emit(*x, 0, 0, &mut seen, &mut out, &mut count);
        emit(0, *x, 0, &mut seen, &mut out, &mut count);
        emit(0, 0, *x, &mut seen, &mut out, &mut count);
        emit(*x, *x, 0, &mut seen, &mut out, &mut count);
        emit(*x, 0, *x, &mut seen, &mut out, &mut count);
        emit(0, *x, *x, &mut seen, &mut out, &mut count);
        emit(*x, *x, *x, &mut seen, &mut out, &mut count);
    }

    // One dominates
    for d in [2_000_000_000i64, 1_999_999_999, 1_000_000_000, 1].iter() {
        for o in [0i64, 1, 2, 3, *d / 4, *d / 2, *d - 1].iter() {
            emit(*d, *o, *o, &mut seen, &mut out, &mut count);
            emit(*o, *d, *o, &mut seen, &mut out, &mut count);
            emit(*o, *o, *d, &mut seen, &mut out, &mut count);
        }
    }

    // Random
    while count < target_count {
        let style = rng.gen_range_i64(0, 5);
        let (r, g, b) = match style {
            0 => (rng.gen_range_i64(0, 100), rng.gen_range_i64(0, 100), rng.gen_range_i64(0, 100)),
            1 => (rng.gen_range_i64(0, 1_000_000), rng.gen_range_i64(0, 1_000_000), rng.gen_range_i64(0, 1_000_000)),
            2 => (rng.gen_range_i64(1_000_000_000, 2_000_000_000), rng.gen_range_i64(0, 2_000_000_000), rng.gen_range_i64(0, 2_000_000_000)),
            3 => (rng.gen_range_i64(1_900_000_000, 2_000_000_000), rng.gen_range_i64(1_900_000_000, 2_000_000_000), rng.gen_range_i64(1_900_000_000, 2_000_000_000)),
            _ => (rng.gen_range_i64(0, 2_000_000_000), rng.gen_range_i64(0, 2_000_000_000), rng.gen_range_i64(0, 2_000_000_000)),
        };
        emit(r, g, b, &mut seen, &mut out, &mut count);
    }
}

