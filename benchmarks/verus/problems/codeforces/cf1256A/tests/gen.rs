use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    seed_a: i64,
    seed_b: i64,
    seed_n: i64,
    seed_s: i64,
    mutation_kind: u8,
) -> (result: (i64, i64, i64, i64))
    ensures
        1 <= result.0 <= 1000000000,
        1 <= result.1 <= 1000000000,
        1 <= result.2 <= 1000000000,
        1 <= result.3 <= 1000000000,
{
    let seed_a = if seed_a < 1 { 1 } else if seed_a > 1000000000 { 1000000000 } else { seed_a };
    let seed_b = if seed_b < 1 { 1 } else if seed_b > 1000000000 { 1000000000 } else { seed_b };
    let seed_n = if seed_n < 1 { 1 } else if seed_n > 1000000000 { 1000000000 } else { seed_n };
    let seed_s = if seed_s < 1 { 1 } else if seed_s > 1000000000 { 1000000000 } else { seed_s };
    let mut a = seed_a;
    let mut b = seed_b;
    let mut n = seed_n;
    let mut s = seed_s;

    if mutation_kind == 0 {
        // identity
    } else if mutation_kind == 1 {
        // nudge a up
        if a < 1000000000 {
            a = a + 1;
        }
    } else if mutation_kind == 2 {
        // nudge a down
        if a > 1 {
            a = a - 1;
        }
    } else if mutation_kind == 3 {
        // nudge b up
        if b < 1000000000 {
            b = b + 1;
        }
    } else if mutation_kind == 4 {
        // nudge b down
        if b > 1 {
            b = b - 1;
        }
    } else if mutation_kind == 5 {
        // set a to min boundary
        a = 1;
    } else if mutation_kind == 6 {
        // set a to max boundary
        a = 1000000000;
    } else if mutation_kind == 7 {
        // set b to min boundary
        b = 1;
    } else if mutation_kind == 8 {
        // set b to max boundary
        b = 1000000000;
    } else if mutation_kind == 9 {
        // set n to min boundary
        n = 1;
    } else if mutation_kind == 10 {
        // set n to max boundary
        n = 1000000000;
    } else if mutation_kind == 11 {
        // set s to min boundary
        s = 1;
    } else if mutation_kind == 12 {
        // set s to max boundary
        s = 1000000000;
    } else if mutation_kind == 13 {
        // halve a
        a = a / 2;
        if a < 1 { a = 1; }
    } else if mutation_kind == 14 {
        // double a (clamped)
        if a <= 500000000 {
            a = a * 2;
        } else {
            a = 1000000000;
        }
    } else if mutation_kind == 15 {
        // halve s
        s = s / 2;
        if s < 1 { s = 1; }
    } else if mutation_kind == 16 {
        // double s (clamped)
        if s <= 500000000 {
            s = s * 2;
        } else {
            s = 1000000000;
        }
    } else if mutation_kind == 17 {
        // all boundaries min
        a = 1;
        b = 1;
        n = 1;
        s = 1;
    } else if mutation_kind == 18 {
        // all boundaries max
        a = 1000000000;
        b = 1000000000;
        n = 1000000000;
        s = 1000000000;
    } else {
        // fallback: identity
    }

    (a, b, n, s)
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

fn build_input(cases: &[(i64,i64,i64,i64)]) -> String {
    let mut s = format!("{}\n", cases.len());
    for &(a,b,n,sv) in cases {
        s.push_str(&format!("{} {} {} {}\n", a, b, n, sv));
    }
    s
}

fn build_output(answers: &[bool]) -> String {
    let mut s = String::new();
    for &a in answers {
        s.push_str(if a { "YES\n" } else { "NO\n" });
    }
    s
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let mut seen: HashSet<u64> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |cases: Vec<(i64,i64,i64,i64)>, seen: &mut HashSet<u64>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        let mut h: u64 = 1469598103934665603;
        h ^= cases.len() as u64; h = h.wrapping_mul(1099511628211);
        for &(a,b,n,sv) in &cases {
            h ^= a as u64; h = h.wrapping_mul(1099511628211);
            h ^= b as u64; h = h.wrapping_mul(1099511628211);
            h ^= n as u64; h = h.wrapping_mul(1099511628211);
            h ^= sv as u64; h = h.wrapping_mul(1099511628211);
        }
        if !seen.insert(h) { return; }
        let answers: Vec<bool> = cases.iter().map(|&(a,b,n,sv)| Solution::payment_without_change(a,b,n,sv)).collect();
        let cases: Vec<_> = cases.into_iter()
            .map(|c| generate_test_case(c.0, c.1, c.2, c.3, 0)).collect();
        let inp = build_input(&cases);
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    // Edge cases
    emit(vec![(1,1,1,1)], &mut seen, &mut out, &mut count);
    emit(vec![(1_000_000_000,1_000_000_000,1_000_000_000,1_000_000_000_000)], &mut seen, &mut out, &mut count);
    emit(vec![(1,1,2,3)], &mut seen, &mut out, &mut count);
    emit(vec![(1,2,3,4)], &mut seen, &mut out, &mut count);

    let mut tries = 0;
    while count < target && tries < 5000 {
        tries += 1;
        let t: usize = if tries < 5 { 1 } else { rng.gen_range_usize(2, 50) };
        let mut cases: Vec<(i64,i64,i64,i64)> = Vec::new();
        for _ in 0..t {
            let max_v = match tries % 4 {
                0 => 10i64,
                1 => 100,
                2 => 1_000_000,
                _ => 1_000_000_000,
            };
            let a = rng.gen_range_i64(1, max_v);
            let b = rng.gen_range_i64(1, max_v);
            let n = rng.gen_range_i64(1, max_v);
            let sv = rng.gen_range_i64(1, max_v * 1000);
            cases.push((a,b,n,sv));
        }
        emit(cases, &mut seen, &mut out, &mut count);
    }
}
