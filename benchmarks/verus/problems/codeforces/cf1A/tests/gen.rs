use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_n: u64, seed_m: u64, seed_a: u64, mutation_kind: u8)
    -> (result: (u64, u64, u64))
    requires
        1 <= seed_n <= 1_000_000_000,
        1 <= seed_m <= 1_000_000_000,
        1 <= seed_a <= 1_000_000_000,
    ensures
        1 <= result.0 <= 1_000_000_000,
        1 <= result.1 <= 1_000_000_000,
        1 <= result.2 <= 1_000_000_000,
{
    let mut n = seed_n;
    let mut m = seed_m;
    let mut a = seed_a;

    if mutation_kind == 0 {
        // identity
    } else if mutation_kind == 1 && n < 1_000_000_000 {
        n = n + 1;                           // nudge n up
    } else if mutation_kind == 2 && n > 1 {
        n = n - 1;                           // nudge n down
    } else if mutation_kind == 3 && m < 1_000_000_000 {
        m = m + 1;                           // nudge m up
    } else if mutation_kind == 4 && m > 1 {
        m = m - 1;                           // nudge m down
    } else if mutation_kind == 5 && a < 1_000_000_000 {
        a = a + 1;                           // nudge a up
    } else if mutation_kind == 6 && a > 1 {
        a = a - 1;                           // nudge a down
    } else if mutation_kind == 7 {
        n = 1;                               // min n
    } else if mutation_kind == 8 {
        n = 1_000_000_000;                   // max n
    } else if mutation_kind == 9 {
        m = 1;                               // min m
    } else if mutation_kind == 10 {
        m = 1_000_000_000;                   // max m
    } else if mutation_kind == 11 {
        a = 1;                               // min a
    } else if mutation_kind == 12 {
        a = 1_000_000_000;                   // max a
    } else if mutation_kind == 13 {
        if n <= 500_000_000 {
            n = n * 2;                       // double n
        }
    } else if mutation_kind == 14 {
        n = n / 2 + 1;                       // halve n (stay >= 1)
    } else if mutation_kind == 15 {
        if m <= 500_000_000 {
            m = m * 2;                       // double m
        }
    } else if mutation_kind == 16 {
        m = m / 2 + 1;                       // halve m (stay >= 1)
    } else if mutation_kind == 17 {
        n = seed_a;
        a = seed_a;                          // n == a (exactly 1 row)
    } else if mutation_kind == 18 {
        m = seed_a;
        a = seed_a;                          // m == a (exactly 1 col)
    } else {
        // fallback: identity
    }

    (n, m, a)
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

    fn gen_range_u64(&mut self, lo: u64, hi: u64) -> u64 {
        let range = (hi - lo + 1) as u128;
        lo + (self.next_u64() as u128 % range) as u64
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

fn build_input(n: u64, m: u64, a: u64) -> String {
    format!("{} {} {}\n", n, m, a)
}

fn build_output(ans: u64) -> String {
    format!("{}\n", ans)
}

fn emit(n: u64, m: u64, a: u64, seen: &mut HashSet<(u64, u64, u64)>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize, target: usize) {
    if *count >= target { return; }
    if !seen.insert((n, m, a)) { return; }
    let inp = build_input(n, m, a);
    let outp = build_output(Solution::min_flagstones(n, m, a));
    writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
    *count += 1;
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut count = 0usize;

    emit(6, 6, 4, &mut seen, &mut out, &mut count, target);
    // Edge cases
    let edges: Vec<(u64, u64, u64)> = vec![
        (1, 1, 1),
        (1, 1, 1_000_000_000),
        (1_000_000_000, 1_000_000_000, 1),
        (1_000_000_000, 1_000_000_000, 1_000_000_000),
        (1, 1_000_000_000, 1_000_000_000),
        (1_000_000_000, 1, 1_000_000_000),
        (1, 1_000_000_000, 1),
        (5, 5, 5),
        (10, 1, 1),
        (1, 10, 1),
        (10, 10, 3),
        (5, 7, 2),
        (12, 13, 5),
        (1_000_000_000, 1_000_000_000, 999_999_999),
    ];
    for (n, m, a) in edges {
        emit(n, m, a, &mut seen, &mut out, &mut count, target);
    }

    while count < target {
        let (n, m, a) = match count % 5 {
            0 => (rng.gen_range_u64(1, 10), rng.gen_range_u64(1, 10), rng.gen_range_u64(1, 10)),
            1 => (rng.gen_range_u64(1, 1000), rng.gen_range_u64(1, 1000), rng.gen_range_u64(1, 1000)),
            2 => (rng.gen_range_u64(1, 1_000_000), rng.gen_range_u64(1, 1_000_000), rng.gen_range_u64(1, 1_000_000)),
            3 => (rng.gen_range_u64(1_000_000, 1_000_000_000), rng.gen_range_u64(1_000_000, 1_000_000_000), rng.gen_range_u64(1_000_000, 1_000_000_000)),
            _ => {
                let boundaries: [u64; 5] = [1, 2, 999_999_999, 1_000_000_000, 500_000_000];
                let n = boundaries[(rng.next_u64() as usize) % 5];
                let m = boundaries[(rng.next_u64() as usize) % 5];
                let a = boundaries[(rng.next_u64() as usize) % 5];
                (n, m, a)
            }
        };
        emit(n, m, a, &mut seen, &mut out, &mut count, target);
    }
}

