use vstd::prelude::*;

verus! {

pub fn generate_test_case(n_seed: i64, m_seed: i64, mutation_kind: u8) -> (result: (i64, i64))
    ensures
        1 <= result.0 as int <= 1000000,
        1 <= result.1 as int <= 1000000,
{
    let n_seed = if n_seed < 1 { 1 } else if n_seed > 1000000 { 1000000 } else { n_seed };
    let m_seed = if m_seed < 1 { 1 } else if m_seed > 1000000 { 1000000 } else { m_seed };
    let n = n_seed;
    let m = m_seed;

    if mutation_kind == 0 {
        (n, m)                                                // identity
    } else if mutation_kind == 1 && n < 1000000 {
        (n + 1, m)                                            // nudge n up
    } else if mutation_kind == 2 && n > 1 {
        (n - 1, m)                                            // nudge n down
    } else if mutation_kind == 3 && m < 1000000 {
        (n, m + 1)                                            // nudge m up
    } else if mutation_kind == 4 && m > 1 {
        (n, m - 1)                                            // nudge m down
    } else if mutation_kind == 5 {
        (1, m)                                                // n = 1 (always YES)
    } else if mutation_kind == 6 {
        (1000000, m)                                    // n = max
    } else if mutation_kind == 7 {
        (n, 1)                                                // m = min
    } else if mutation_kind == 8 {
        (n, 1000000)                                    // m = max
    } else if mutation_kind == 9 {
        (1, 1)                                                // both min
    } else if mutation_kind == 10 {
        (1000000, 1000000)                        // both max
    } else if mutation_kind == 11 {
        // swap n and m
        (m, n)
    } else if mutation_kind == 12 {
        // n = m (boundary: m >= n triggers false)
        (m, m)
    } else if mutation_kind == 13 && n >= 2 && n <= 500000 {
        // double n
        (n * 2, m)
    } else if mutation_kind == 14 {
        // halve n
        let half = n / 2;
        if half >= 1 { (half, m) } else { (1, m) }
    } else if mutation_kind == 15 && m >= 2 && m <= 500000 {
        // double m
        (n, m * 2)
    } else if mutation_kind == 16 {
        // halve m
        let half = m / 2;
        if half >= 1 { (n, half) } else { (n, 1) }
    } else {
        (n, m)                                                // fallback
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

fn pick_n_m(rng: &mut Rng, mode: u8) -> (i64, i64) {
    match mode % 11 {
        0 => (1, rng.gen_range_i64(1, 1_000_000_000)),
        1 => (rng.gen_range_i64(2, 1_000_000_000), 1),
        2 => {
            let v = rng.gen_range_i64(2, 1_000_000_000);
            (v, v)
        }
        3 => {
            let primes: [i64; 16] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 97, 101, 9973, 999983, 999_999_937];
            let n = primes[(rng.next_u64() as usize) % primes.len()];
            let m = rng.gen_range_i64(1, n.max(2));
            (n, m)
        }
        4 => {
            let ns: [i64; 13] = [4, 6, 8, 9, 10, 12, 15, 16, 25, 100, 1000, 1_000_000, 999_999_999];
            let n = ns[(rng.next_u64() as usize) % ns.len()];
            let m = rng.gen_range_i64(1, n);
            (n, m)
        }
        5 => (rng.gen_range_i64(1, 1_000_000_000), rng.gen_range_i64(1, 1_000_000_000)),
        6 => (2 * 499_999_993, rng.gen_range_i64(1, 1_000_000_000)),
        7 => (1_000_000_000, 1_000_000_000),
        8 => {
            let m = rng.gen_range_i64(1, 999_999_999);
            (m + 1, m)
        }
        9 => (rng.gen_range_i64(1, 100), rng.gen_range_i64(1, 1_000_000_000)),
        _ => {
            let k = rng.gen_range_i64(2, 31622);
            (k * k, rng.gen_range_i64(1, k))
        }
    }
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
        if a { s.push_str("YES\n"); } else { s.push_str("NO\n"); }
    }
    s
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let mut seen: HashSet<String> = HashSet::new();

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    // First entry = the example from description
    let example: Vec<(i64, i64)> = vec![(3, 2), (4, 2), (5, 3), (1_000_000, 1_000_000), (1, 1_000_000)];
    {
        let answers: Vec<bool> = example.iter().map(|&(n, m)| Solution::freedom_possible(m, n)).collect();
        let example: Vec<_> = example.into_iter()
            .map(|c| generate_test_case(c.0, c.1, 0)).collect();
        let inp = build_input(&example);
        let outs = build_output(&answers);
        if seen.insert(inp.clone()) {
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
            count += 1;
        }
    }

    // Some single-test entries (t=1) covering edge cases
    let single_cases: Vec<(i64, i64)> = vec![
        (1, 1), (2, 1), (2, 2), (1_000_000_000, 1), (1_000_000_000, 1_000_000_000),
        (999_999_937, 999_999_936), (999_999_999, 3), (4, 2), (6, 5), (7, 2),
    ];
    for &c in &single_cases {
        if count >= target { break; }
        let cases = vec![c];
        let answers: Vec<bool> = cases.iter().map(|&(n, m)| Solution::freedom_possible(m, n)).collect();
        let cases: Vec<_> = cases.into_iter()
            .map(|c| generate_test_case(c.0, c.1, 0)).collect();
        let inp = build_input(&cases);
        let outs = build_output(&answers);
        if seen.insert(inp.clone()) {
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
            count += 1;
        }
    }

    // Bundled multi-test entries
    while count < target {
        let t: usize = if count < 20 { rng.gen_range_usize(2, 8) } else { rng.gen_range_usize(5, 30) };
        let mut cases: Vec<(i64, i64)> = Vec::new();
        for i in 0..t {
            let mode = (rng.gen_range_i64(0, 1000) % 11) as u8;
            let (n, m) = pick_n_m(&mut rng, mode.wrapping_add(i as u8));
            cases.push((n, m));
        }
        let cases: Vec<_> = cases.into_iter()
            .map(|c| generate_test_case(c.0, c.1, 0)).collect();
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<bool> = cases.iter().map(|&(n, m)| Solution::freedom_possible(m, n)).collect();
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}
