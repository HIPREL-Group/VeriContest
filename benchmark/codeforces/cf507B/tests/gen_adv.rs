use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    r: i128,
    x: i128,
    y: i128,
    x2: i128,
    y2: i128,
) -> (res: (i128, i128, i128, i128, i128))
    requires
        1 <= r <= 100000,
        -100000 <= x <= 100000,
        -100000 <= y <= 100000,
        -100000 <= x2 <= 100000,
        -100000 <= y2 <= 100000,
    ensures
        1 <= res.0 <= 100000,
        -100000 <= res.1 <= 100000,
        -100000 <= res.2 <= 100000,
        -100000 <= res.3 <= 100000,
        -100000 <= res.4 <= 100000,
{
    (r, x, y, x2, y2)
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
    let mut rng = Rng::new(50703);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen: HashSet<String> = HashSet::new();
    let mut count = 0usize;

    let mut emit = |r: i128, x: i128, y: i128, x2: i128, y2: i128, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count { return; }
        if r < 1 || r > 100_000 { return; }
        if x < -100_000 || x > 100_000 || y < -100_000 || y > 100_000 { return; }
        if x2 < -100_000 || x2 > 100_000 || y2 < -100_000 || y2 > 100_000 { return; }
        let key = format!("{}_{}_{}_{}_{}", r, x, y, x2, y2);
        if !seen.insert(key) { return; }
        let result = Solution::min_steps_to_target(r, x, y, x2, y2);
        let inp = format!("{} {} {} {} {}\n", r, x, y, x2, y2);
        let outp = format!("{}\n", result);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    // Adversarial: very small r, max distance
    emit(1, -100_000, -100_000, 100_000, 100_000, &mut seen, &mut out, &mut count);
    emit(1, -100_000, 0, 100_000, 0, &mut seen, &mut out, &mut count);
    emit(1, 0, 0, 100_000, 100_000, &mut seen, &mut out, &mut count);
    // Boundary cases for distance just at multiples of 2r
    for r in [1i128, 2, 5, 10, 100, 1000, 10000, 100000].iter() {
        for k in 0..=5 {
            let dx = 2 * *r * k;
            if dx <= 100_000 && dx >= -100_000 {
                emit(*r, 0, 0, dx, 0, &mut seen, &mut out, &mut count);
                if dx > 0 {
                    emit(*r, 0, 0, dx - 1, 0, &mut seen, &mut out, &mut count);
                    emit(*r, 0, 0, dx + 1, 0, &mut seen, &mut out, &mut count);
                }
            }
        }
    }

    while count < target_count {
        let r = match count % 4 {
            0 => 1,
            1 => rng.gen_range_i64(1, 10) as i128,
            2 => rng.gen_range_i64(1, 1000) as i128,
            _ => rng.gen_range_i64(1, 100_000) as i128,
        };
        let x = rng.gen_range_i64(-100_000, 100_000) as i128;
        let y = rng.gen_range_i64(-100_000, 100_000) as i128;
        let x2 = rng.gen_range_i64(-100_000, 100_000) as i128;
        let y2 = rng.gen_range_i64(-100_000, 100_000) as i128;
        emit(r, x, y, x2, y2, &mut seen, &mut out, &mut count);
    }
}

