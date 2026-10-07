use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_n: u64, seed_m: u64, seed_x: u64, mutation_kind: u8) -> (result: (u64, u64, u64))
    requires
        1 <= seed_n <= 1_000_000,
        1 <= seed_m <= 1_000_000,
        1 <= seed_x <= seed_n * seed_m,
    ensures
        1 <= result.0 <= 1_000_000,
        1 <= result.1 <= 1_000_000,
        1 <= result.2 <= result.0 * result.1,
{
    proof {
        assert(seed_n * seed_m <= 1_000_000 * 1_000_000u64) by(nonlinear_arith)
            requires seed_n <= 1_000_000, seed_m <= 1_000_000, seed_n >= 1, seed_m >= 1;
    }
    if mutation_kind == 0 {
        // identity
        proof {
            assert(seed_x <= seed_n * seed_m) by(nonlinear_arith)
                requires seed_x <= seed_n * seed_m;
        }
        (seed_n, seed_m, seed_x)
    } else if mutation_kind == 1 && seed_n < 1_000_000 {
        // nudge n up
        proof {
            assert((seed_n + 1) * seed_m >= seed_n * seed_m) by(nonlinear_arith)
                requires seed_n >= 1, seed_m >= 1;
        }
        (seed_n + 1, seed_m, seed_x)
    } else if mutation_kind == 2 && seed_m < 1_000_000 {
        // nudge m up
        proof {
            assert(seed_n * (seed_m + 1) >= seed_n * seed_m) by(nonlinear_arith)
                requires seed_n >= 1, seed_m >= 1;
        }
        (seed_n, seed_m + 1, seed_x)
    } else if mutation_kind == 3 {
        // x = 1 (minimum x)
        proof {
            assert(1 <= seed_n * seed_m) by(nonlinear_arith)
                requires seed_n >= 1, seed_m >= 1;
        }
        (seed_n, seed_m, 1)
    } else if mutation_kind == 4 {
        // x = n*m (maximum x)
        (seed_n, seed_m, seed_n * seed_m)
    } else if mutation_kind == 5 {
        // n = 1
        proof {
            assert(1u64 * seed_m == seed_m) by(nonlinear_arith);
        }
        (1, seed_m, if seed_x <= seed_m { seed_x } else { seed_m })
    } else if mutation_kind == 6 {
        // m = 1
        proof {
            assert(seed_n * 1u64 == seed_n) by(nonlinear_arith);
        }
        (seed_n, 1, if seed_x <= seed_n { seed_x } else { seed_n })
    } else if mutation_kind == 7 {
        // n = 1, m = 1, x = 1
        proof {
            assert(1u64 * 1u64 == 1u64) by(nonlinear_arith);
        }
        (1, 1, 1)
    } else if mutation_kind == 8 && seed_n > 1 {
        // nudge n down, clamp x
        proof {
            assert((seed_n - 1) * seed_m >= 1) by(nonlinear_arith)
                requires seed_n > 1, seed_m >= 1;
            assert((seed_n - 1) * seed_m <= seed_n * seed_m) by(nonlinear_arith)
                requires seed_n >= 1, seed_m >= 1;
        }
        let max_x = (seed_n - 1) * seed_m;
        (seed_n - 1, seed_m, if seed_x <= max_x { seed_x } else { max_x })
    } else if mutation_kind == 9 && seed_m > 1 {
        // nudge m down, clamp x
        proof {
            assert(seed_n * (seed_m - 1) >= 1) by(nonlinear_arith)
                requires seed_n >= 1, seed_m > 1;
            assert(seed_n * (seed_m - 1) <= seed_n * seed_m) by(nonlinear_arith)
                requires seed_n >= 1, seed_m >= 1;
        }
        let max_x = seed_n * (seed_m - 1);
        (seed_n, seed_m - 1, if seed_x <= max_x { seed_x } else { max_x })
    } else if mutation_kind == 10 {
        // x = n (first column filled)
        proof {
            assert(seed_n <= seed_n * seed_m) by(nonlinear_arith)
                requires seed_n >= 1, seed_m >= 1;
        }
        (seed_n, seed_m, seed_n)
    } else if mutation_kind == 11 {
        // x = m
        proof {
            assert(seed_m <= seed_n * seed_m) by(nonlinear_arith)
                requires seed_n >= 1, seed_m >= 1;
        }
        (seed_n, seed_m, seed_m)
    } else {
        // fallback
        proof {
            assert(seed_x <= seed_n * seed_m) by(nonlinear_arith)
                requires seed_x <= seed_n * seed_m;
        }
        (seed_n, seed_m, seed_x)
    }
}

}

use std::io::Write;

struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0
    }
    fn gen_range_u64(&mut self, lo: u64, hi: u64) -> u64 {
        let r = hi - lo + 1;
        lo + self.next_u64() % r
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

fn build_input(cases: &[(u64, u64, u64)]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (n, m, x) in cases {
        s.push_str(&format!("{} {} {}\n", n, m, x));
    }
    s
}

fn build_output(answers: &[u64]) -> String {
    let mut s = String::new();
    for a in answers {
        s.push_str(&format!("{}\n", a));
    }
    s
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);

    // Examples
    {
        let cases: Vec<(u64, u64, u64)> = vec![
            (6, 5, 10), (6, 5, 20), (6, 5, 26), (6, 5, 15), (6, 5, 24),
        ];
        let answers: Vec<u64> = cases.iter().map(|&(n, m, x)| Solution::strange_table_number(n, m, x)).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
    }

    let mut count = 1usize;

    let edges: Vec<(u64, u64, u64)> = vec![
        (1, 1, 1),
        (1, 1_000_000, 500_000),
        (1_000_000, 1, 500_000),
        (1_000_000, 1_000_000, 1),
        (1_000_000, 1_000_000, 1_000_000_000_000),
        (10, 10, 50),
    ];
    for e in edges {
        if count >= target { break; }
        let cases = vec![e];
        let answers: Vec<u64> = cases.iter().map(|&(n, m, x)| Solution::strange_table_number(n, m, x)).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }

    while count < target {
        let t: usize = if count < 20 { 1 } else { rng.gen_range_usize(2, 30) };
        let mut cases: Vec<(u64, u64, u64)> = Vec::new();
        for _ in 0..t {
            let mode = rng.next_u64() % 4;
            let (n, m) = match mode {
                0 => (rng.gen_range_u64(1, 10), rng.gen_range_u64(1, 10)),
                1 => (rng.gen_range_u64(1, 1000), rng.gen_range_u64(1, 1000)),
                2 => (rng.gen_range_u64(1, 100000), rng.gen_range_u64(1, 100000)),
                _ => (rng.gen_range_u64(1, 1_000_000), rng.gen_range_u64(1, 1_000_000)),
            };
            let total = n.saturating_mul(m).max(1);
            let x = rng.gen_range_u64(1, total);
            cases.push((n, m, x));
        }
        let answers: Vec<u64> = cases.iter().map(|&(n, m, x)| Solution::strange_table_number(n, m, x)).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

