use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_w: i64, seed_m: i64, mutation_kind: u8)
    -> (result: (i64, i64))
    requires
        2 <= seed_w <= 1_000_000_000,
        1 <= seed_m <= 1_000_000_000,
    ensures
        2 <= result.0 <= 1_000_000_000,
        1 <= result.1 <= 1_000_000_000,
{
    let mut w = seed_w;
    let mut m = seed_m;

    if mutation_kind == 0 {
        // identity
    } else if mutation_kind == 1 && w < 1_000_000_000 {
        w = w + 1;                               // nudge w up
    } else if mutation_kind == 2 && w > 2 {
        w = w - 1;                               // nudge w down
    } else if mutation_kind == 3 && m < 1_000_000_000 {
        m = m + 1;                               // nudge m up
    } else if mutation_kind == 4 && m > 1 {
        m = m - 1;                               // nudge m down
    } else if mutation_kind == 5 {
        w = 2;                                   // min w
    } else if mutation_kind == 6 {
        w = 1_000_000_000;                       // max w
    } else if mutation_kind == 7 {
        m = 1;                                   // min m
    } else if mutation_kind == 8 {
        m = 1_000_000_000;                       // max m
    } else if mutation_kind == 9 {
        if w <= 500_000_000 {
            w = w * 2;                           // double w
        }
    } else if mutation_kind == 10 {
        w = w / 2 + 1;                           // halve w (stay >= 2)
    } else if mutation_kind == 11 {
        if m <= 500_000_000 {
            m = m * 2;                           // double m
        }
    } else if mutation_kind == 12 {
        m = m / 2 + 1;                           // halve m (stay >= 1)
    } else if mutation_kind == 13 {
        m = seed_w;
        w = seed_w;                              // m == w
    } else if mutation_kind == 14 {
        w = 3;                                   // w=3 (base-3 representation)
    } else if mutation_kind == 15 {
        w = 10;                                  // w=10 (base-10)
    } else {
        // fallback: identity
    }

    (w, m)
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
    let target_count: usize = 100;
    let mut rng = Rng::new(552);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
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

    emit(3, 7, &mut seen, &mut out, &mut count);
    emit(100, 99, &mut seen, &mut out, &mut count);
    emit(100, 50, &mut seen, &mut out, &mut count);

    // Edge
    emit(2, 1, &mut seen, &mut out, &mut count);
    emit(2, 1_000_000_000, &mut seen, &mut out, &mut count);
    emit(1_000_000_000, 1, &mut seen, &mut out, &mut count);
    emit(1_000_000_000, 1_000_000_000, &mut seen, &mut out, &mut count);
    emit(3, 1, &mut seen, &mut out, &mut count);
    emit(3, 2, &mut seen, &mut out, &mut count);
    emit(3, 3, &mut seen, &mut out, &mut count);
    emit(3, 4, &mut seen, &mut out, &mut count);
    emit(3, 5, &mut seen, &mut out, &mut count);
    emit(4, 5, &mut seen, &mut out, &mut count);
    emit(5, 13, &mut seen, &mut out, &mut count);

    while count < target_count {
        let w = rng.gen_range_i64(2, 1_000_000_000);
        let m = rng.gen_range_i64(1, 1_000_000_000);
        emit(w, m, &mut seen, &mut out, &mut count);
    }
}

