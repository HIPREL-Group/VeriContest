use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    seed_a: i64, seed_b: i64, seed_k: i64, mutation_kind: u8,
) -> (result: (i64, i64, i64))
    requires
        1 <= seed_a <= 1_000_000_000,
        1 <= seed_b <= 1_000_000_000,
        1 <= seed_k <= 1_000_000_000,
    ensures
        1 <= result.0 <= 1_000_000_000,
        1 <= result.1 <= 1_000_000_000,
        1 <= result.2 <= 1_000_000_000,
{
    let a: i64;
    let b: i64;
    let k: i64;

    if mutation_kind == 0 {
        // identity
        a = seed_a;
        b = seed_b;
        k = seed_k;
    } else if mutation_kind == 1 && seed_a < 1_000_000_000 {
        // nudge a up
        a = seed_a + 1;
        b = seed_b;
        k = seed_k;
    } else if mutation_kind == 2 && seed_a > 1 {
        // nudge a down
        a = seed_a - 1;
        b = seed_b;
        k = seed_k;
    } else if mutation_kind == 3 && seed_b < 1_000_000_000 {
        // nudge b up
        a = seed_a;
        b = seed_b + 1;
        k = seed_k;
    } else if mutation_kind == 4 && seed_b > 1 {
        // nudge b down
        a = seed_a;
        b = seed_b - 1;
        k = seed_k;
    } else if mutation_kind == 5 && seed_k < 1_000_000_000 {
        // nudge k up
        a = seed_a;
        b = seed_b;
        k = seed_k + 1;
    } else if mutation_kind == 6 && seed_k > 1 {
        // nudge k down
        a = seed_a;
        b = seed_b;
        k = seed_k - 1;
    } else if mutation_kind == 7 {
        // min boundary for a
        a = 1;
        b = seed_b;
        k = seed_k;
    } else if mutation_kind == 8 {
        // max boundary for a
        a = 1_000_000_000;
        b = seed_b;
        k = seed_k;
    } else if mutation_kind == 9 {
        // min boundary for b
        a = seed_a;
        b = 1;
        k = seed_k;
    } else if mutation_kind == 10 {
        // max boundary for b
        a = seed_a;
        b = 1_000_000_000;
        k = seed_k;
    } else if mutation_kind == 11 {
        // min boundary for k
        a = seed_a;
        b = seed_b;
        k = 1;
    } else if mutation_kind == 12 {
        // max boundary for k
        a = seed_a;
        b = seed_b;
        k = 1_000_000_000;
    } else if mutation_kind == 13 {
        // a = b (symmetric jumps)
        a = seed_a;
        b = seed_a;
        k = seed_k;
    } else if mutation_kind == 14 {
        // halve a
        let ha = seed_a / 2;
        a = if ha >= 1 { ha } else { 1 };
        b = seed_b;
        k = seed_k;
    } else if mutation_kind == 15 {
        // halve b
        a = seed_a;
        let hb = seed_b / 2;
        b = if hb >= 1 { hb } else { 1 };
        k = seed_k;
    } else if mutation_kind == 16 {
        // halve k
        a = seed_a;
        b = seed_b;
        let hk = seed_k / 2;
        k = if hk >= 1 { hk } else { 1 };
    } else if mutation_kind == 17 {
        // all min
        a = 1;
        b = 1;
        k = 1;
    } else if mutation_kind == 18 {
        // all max
        a = 1_000_000_000;
        b = 1_000_000_000;
        k = 1_000_000_000;
    } else {
        // fallback: identity
        a = seed_a;
        b = seed_b;
        k = seed_k;
    }

    (a, b, k)
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

fn build_input_multi(cases: &[(i64,i64,i64)]) -> String {
    let mut s = format!("{}\n", cases.len());
    for &(a,b,k) in cases {
        s.push_str(&format!("{} {} {}\n", a, b, k));
    }
    s
}

fn build_output_multi(ans: &[i64]) -> String {
    let mut s = String::new();
    for a in ans {
        s.push_str(&format!("{}\n", a));
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

    let mut emit = |cases: Vec<(i64,i64,i64)>, seen: &mut HashSet<u64>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        let mut h: u64 = 1469598103934665603;
        h ^= cases.len() as u64;
        h = h.wrapping_mul(1099511628211);
        for &(a,b,k) in &cases {
            h ^= a as u64; h = h.wrapping_mul(1099511628211);
            h ^= b as u64; h = h.wrapping_mul(1099511628211);
            h ^= k as u64; h = h.wrapping_mul(1099511628211);
        }
        if !seen.insert(h) { return; }
        let answers: Vec<i64> = cases.iter().map(|&(a,b,k)| Solution::frog_position_after_jumps(a,b,k)).collect();
        let inp = build_input_multi(&cases);
        let outs = build_output_multi(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    // Example
    let example = vec![(5,2,3),(100,1,4),(1,10,5),(1_000_000_000,1,6),(1,1,1_000_000_000),(1,1,999_999_999)];
    emit(example, &mut seen, &mut out, &mut count);

    // Edge cases as singletons
    emit(vec![(1,1,1)], &mut seen, &mut out, &mut count);
    emit(vec![(1_000_000_000,1_000_000_000,1_000_000_000)], &mut seen, &mut out, &mut count);
    emit(vec![(1,1,2)], &mut seen, &mut out, &mut count);

    // Mix t=1 to t=50
    while count < target {
        let t: usize = if count < 5 { 1 } else { rng.gen_range_usize(2, 50) };
        let mut cases: Vec<(i64,i64,i64)> = Vec::new();
        for _ in 0..t {
            let max_v = match count % 4 {
                0 => 100i64,
                1 => 10_000,
                2 => 1_000_000,
                _ => 1_000_000_000,
            };
            let a = rng.gen_range_i64(1, max_v);
            let b = rng.gen_range_i64(1, max_v);
            let k = rng.gen_range_i64(1, max_v);
            cases.push((a,b,k));
        }
        emit(cases, &mut seen, &mut out, &mut count);
    }
}

