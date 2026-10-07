use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_n: i64, seed_m: i64, mutation_kind: u8) -> (result: (i64, i64))
    ensures
        1 <= result.0 <= 10000000,
        1 <= result.1 <= 10000000,
{
    let seed_n = if seed_n < 1 { 1 } else if seed_n > 10000000 { 10000000 } else { seed_n };
    let seed_m = if seed_m < 1 { 1 } else if seed_m > 10000000 { 10000000 } else { seed_m };
    if mutation_kind == 0 {
        // identity
        (seed_n, seed_m)
    } else if mutation_kind == 1 && seed_n < 10000000 {
        // nudge n up
        (seed_n + 1, seed_m)
    } else if mutation_kind == 2 && seed_n > 1 {
        // nudge n down
        (seed_n - 1, seed_m)
    } else if mutation_kind == 3 && seed_m < 10000000 {
        // nudge m up
        (seed_n, seed_m + 1)
    } else if mutation_kind == 4 && seed_m > 1 {
        // nudge m down
        (seed_n, seed_m - 1)
    } else if mutation_kind == 5 {
        // set n = m (equal case, always YES)
        (seed_m, seed_m)
    } else if mutation_kind == 6 {
        // set m = 1 (boundary for m)
        (seed_n, 1)
    } else if mutation_kind == 7 {
        // set n = 1 (boundary for n)
        (1, seed_m)
    } else if mutation_kind == 8 {
        // max boundary for both
        (10000000, 10000000)
    } else if mutation_kind == 9 {
        // min boundary for both
        (1, 1)
    } else if mutation_kind == 10 {
        // n divisible by 3: use seed_n / 3 * 3 if >= 3, else seed_n
        if seed_n >= 3 {
            ((seed_n / 3) * 3, seed_m)
        } else {
            (seed_n, seed_m)
        }
    } else if mutation_kind == 11 {
        // swap n and m
        (seed_m, seed_n)
    } else if mutation_kind == 12 {
        // m = n / 3 (if n >= 3 and n divisible by 3)
        if seed_n >= 3 && seed_n % 3 == 0 {
            (seed_n, seed_n / 3)
        } else {
            (seed_n, seed_m)
        }
    } else if mutation_kind == 13 {
        // m = n - n/3 (the other split piece)
        if seed_n >= 3 && seed_n % 3 == 0 {
            (seed_n, seed_n - seed_n / 3)
        } else {
            (seed_n, seed_m)
        }
    } else {
        // fallback: identity
        (seed_n, seed_m)
    }
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

// Note: main.rs calls Solution::can_obtain(m, n) where (n, m) come from input.
// Input order is n then m. In Solution::can_obtain(m, n), the first arg is target, the second is current pile size.
// So call as Solution::can_obtain(m_input, n_input).
fn solve(n: i64, m: i64) -> bool {
    Solution::can_obtain(m, n)
}

fn build_input(cases: &[(i64, i64)]) -> String {
    let mut s = format!("{}\n", cases.len());
    for &(n, m) in cases {
        s.push_str(&format!("{} {}\n", n, m));
    }
    s
}

fn build_output(answers: &[bool]) -> String {
    let mut s = String::new();
    for &a in answers {
        s.push_str(if a {"YES\n"} else {"NO\n"});
    }
    s
}

fn pick_n_m(rng: &mut Rng, mode: u8) -> (i64, i64) {
    match mode % 8 {
        0 => {
            // n = 3^k for varying k
            let mut n = 1i64;
            let k = rng.gen_range_i64(0, 18);
            for _ in 0..k { n *= 3; }
            let m = rng.gen_range_i64(1, n);
            (n, m)
        }
        1 => {
            // n = m
            let v = rng.gen_range_i64(1, 1_000_000_000);
            (v, v)
        }
        2 => {
            // m > n
            let n = rng.gen_range_i64(1, 1_000_000_000);
            let m = rng.gen_range_i64(n, 1_000_000_000);
            (n, m)
        }
        3 => {
            // n divisible by 3
            let k = rng.gen_range_i64(1, 333_333_333);
            (3 * k, rng.gen_range_i64(1, 3 * k))
        }
        4 => {
            // n not div by 3
            let n = rng.gen_range_i64(1, 1_000_000_000);
            let n = if n % 3 == 0 { n + 1 } else { n };
            (n, rng.gen_range_i64(1, n))
        }
        5 => (1, rng.gen_range_i64(1, 1_000_000_000)),
        6 => (rng.gen_range_i64(1, 1_000_000_000), 1),
        _ => (rng.gen_range_i64(1, 1_000_000_000), rng.gen_range_i64(1, 1_000_000_000)),
    }
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(1829);
    let mut seen: HashSet<String> = HashSet::new();

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    // Hand-crafted examples
    let example_cases: Vec<(i64, i64)> = vec![
        (3, 1), (3, 2), (3, 3), (9, 2), (9, 3), (9, 6), (1, 1), (6, 4),
    ];
    {
        let answers: Vec<bool> = example_cases.iter().map(|&(n, m)| solve(n, m)).collect();
        let example_cases: Vec<_> = example_cases.into_iter()
            .map(|c| generate_test_case(c.0, c.1, 0)).collect();
        let inp = build_input(&example_cases);
        let outs = build_output(&answers);
        if seen.insert(inp.clone()) {
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
            count += 1;
        }
    }

    // Single-test edge cases
    let edge: Vec<(i64, i64)> = vec![
        (1, 1), (2, 1), (3, 1), (3, 2), (1_000_000_000, 1),
        (387_420_489, 1), // 3^18 = 387420489
        (729, 32), // 3^6=729, can split many ways
        (729, 486), // 3^6, 2*243
    ];
    for &c in &edge {
        if count >= target { break; }
        let cases = vec![c];
        let cases: Vec<_> = cases.into_iter()
            .map(|c| generate_test_case(c.0, c.1, 0)).collect();
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<bool> = cases.iter().map(|&(n, m)| solve(n, m)).collect();
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }

    // Bundled multi-test
    while count < target {
        let t: usize = if count < 20 { rng.gen_range_usize(2, 6) } else { rng.gen_range_usize(5, 30) };
        let mut cases: Vec<(i64, i64)> = Vec::new();
        for i in 0..t {
            let mode = (rng.gen_range_i64(0, 100) + i as i64) as u8;
            cases.push(pick_n_m(&mut rng, mode));
        }
        let cases: Vec<_> = cases.into_iter()
            .map(|c| generate_test_case(c.0, c.1, 0)).collect();
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<bool> = cases.iter().map(|&(n, m)| solve(n, m)).collect();
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}
