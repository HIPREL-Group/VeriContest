use vstd::prelude::*;

verus! {

pub fn generate_test_case(w_val: i64, m_val: i64) -> (result: (i64, i64))
    requires
        2 <= w_val <= 1_000_000_000,
        1 <= m_val <= 1_000_000_000,
    ensures
        2 <= result.0 <= 1_000_000_000,
        1 <= result.1 <= 1_000_000_000,
{
    (w_val, m_val)
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
    let mut rng = Rng::new(55205);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen: HashSet<String> = HashSet::new();
    let mut count = 0usize;

    let mut emit = |w: i64, m: i64, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count { return; }
        if w < 2 || w > 1_000_000_000 || m < 1 || m > 1_000_000_000 { return; }
        let key = format!("{}_{}", w, m);
        if !seen.insert(key) { return; }
        let result = Solution::can_balance(w, m);
        let inp = format!("{} {}\n", w, m);
        let outp = if result { "YES\n".to_string() } else { "NO\n".to_string() };
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    // Adversarial: powers of w and almost-powers
    for w in [2i64, 3, 4, 5, 7, 10, 100, 1_000, 100_000, 1_000_000_000].iter() {
        let mut p: i64 = 1;
        for _ in 0..15 {
            p = p.saturating_mul(*w);
            if p > 1_000_000_000 { break; }
            emit(*w, p, &mut seen, &mut out, &mut count);
            if p > 1 {
                emit(*w, p - 1, &mut seen, &mut out, &mut count);
                emit(*w, p + 1, &mut seen, &mut out, &mut count);
            }
        }
    }

    // m near max
    for m in [1_000_000_000i64, 999_999_999, 1].iter() {
        for w in [2i64, 3, 5, 10, 100, 1_000_000_000].iter() {
            emit(*w, *m, &mut seen, &mut out, &mut count);
        }
    }

    // m=1 always solvable (use weight w^0)
    for w in [2i64, 3, 5, 10, 100, 1_000_000_000].iter() {
        emit(*w, 1, &mut seen, &mut out, &mut count);
    }

    // Random
    while count < target_count {
        let w = match count % 4 {
            0 => 2,
            1 => rng.gen_range_i64(2, 10),
            2 => rng.gen_range_i64(2, 10000),
            _ => rng.gen_range_i64(2, 1_000_000_000),
        };
        let m = rng.gen_range_i64(1, 1_000_000_000);
        emit(w, m, &mut seen, &mut out, &mut count);
    }
}

