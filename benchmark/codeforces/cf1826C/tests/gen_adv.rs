use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i64, m: i64) -> (res: (i64, i64))
    ensures
        1 <= res.0 as int <= 1000000,
        1 <= res.1 as int <= 1000000,
{
    let n = if n < 1 { 1 } else if n > 1000000 { 1000000 } else { n };
    let m = if m < 1 { 1 } else if m > 1000000 { 1000000 } else { m };
    (n, m)
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

fn pick_adv(rng: &mut Rng, mode: u8) -> (i64, i64) {
    match mode % 13 {
        0 => (1, 1_000_000_000),
        1 => (1_000_000_000, 1),
        2 => (1_000_000_000, 1_000_000_000),
        3 => {
            // Large prime n
            let primes: [i64; 4] = [999_999_937, 999_999_893, 999_999_751, 999_999_677];
            let n = primes[(rng.next_u64() as usize) % primes.len()];
            (n, rng.gen_range_i64(1, 1_000_000_000))
        }
        4 => {
            // 2 * large prime
            (2 * 499_999_993, rng.gen_range_i64(1, 1_000_000_000))
        }
        5 => {
            // n = small prime^2
            let primes: [i64; 6] = [2, 3, 5, 7, 11, 13];
            let p = primes[(rng.next_u64() as usize) % primes.len()];
            (p * p, rng.gen_range_i64(1, p))
        }
        6 => {
            // n large square
            let k = rng.gen_range_i64(30000, 31622);
            (k * k, rng.gen_range_i64(1, k))
        }
        7 => {
            // n just above m
            let m = rng.gen_range_i64(1, 999_999_999);
            (m + 1, m)
        }
        8 => {
            // n = m
            let v = rng.gen_range_i64(2, 1_000_000_000);
            (v, v)
        }
        9 => {
            // small composite n
            let ns: [i64; 10] = [4, 6, 8, 9, 10, 12, 15, 16, 25, 100];
            let n = ns[(rng.next_u64() as usize) % ns.len()];
            (n, rng.gen_range_i64(1, n))
        }
        10 => (rng.gen_range_i64(1, 1_000_000_000), rng.gen_range_i64(1, 1_000_000_000)),
        11 => {
            // n is highly composite
            let hcs: [i64; 8] = [12, 24, 36, 48, 120, 720, 5040, 720720];
            let n = hcs[(rng.next_u64() as usize) % hcs.len()];
            (n, rng.gen_range_i64(1, n))
        }
        _ => {
            // n = 2^k
            let k = rng.gen_range_i64(1, 29);
            (1i64 << k, rng.gen_range_i64(1, 1i64 << k))
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
    let target: usize = 200;
    let mut rng = Rng::new(2025);
    let mut seen: HashSet<String> = HashSet::new();

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    // Single big-test entries (t = 1, large values)
    let big_singles: Vec<(i64, i64)> = vec![
        (999_999_937, 999_999_936),
        (1_000_000_000, 999_999_999),
        (1_000_000_000, 1_000_000_000),
        (2 * 499_999_993, 999_999_999),
        (1_000_000_000, 1),
    ];
    for &c in &big_singles {
        if count >= target { break; }
        let cases = vec![c];
        let answers: Vec<bool> = cases.iter().map(|&(n, m)| Solution::freedom_possible(m, n)).collect();
        let cases: Vec<_> = cases.into_iter()
            .map(|c| generate_test_case(c.0, c.1)).collect();
        let inp = build_input(&cases);
        let outs = build_output(&answers);
        if seen.insert(inp.clone()) {
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
            count += 1;
        }
    }

    // Bulk: many adversarial test cases bundled together
    while count < target {
        let t: usize = if count < 30 { rng.gen_range_usize(10, 30) } else { rng.gen_range_usize(20, 50) };
        let mut cases: Vec<(i64, i64)> = Vec::new();
        for i in 0..t {
            let mode = ((rng.gen_range_i64(0, 100) + i as i64) % 13) as u8;
            cases.push(pick_adv(&mut rng, mode));
        }
        let cases: Vec<_> = cases.into_iter()
            .map(|c| generate_test_case(c.0, c.1)).collect();
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<bool> = cases.iter().map(|&(n, m)| Solution::freedom_possible(m, n)).collect();
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}
