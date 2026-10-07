use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_n: i64, seed_k: i64, seed_m: i64, mutation_kind: u8) -> (result: (i64, i64, i64))
    requires
        2 <= seed_n <= 1_000_000_000i64,
        2 <= seed_k <= 1_000_000_000i64,
        0 <= seed_m <= 1_000_000_000i64,
    ensures
        2 <= result.2 <= result.0 <= 1_000_000_000,
        0 <= result.1 <= result.0,
{
    // Base construction: clamp k <= n, m <= n
    let n = seed_n;
    let k = if seed_k <= seed_n { seed_k } else { seed_n };
    let m = if seed_m <= seed_n { seed_m } else { seed_n };

    if mutation_kind == 0 {
        // identity
        (n, m, k)
    } else if mutation_kind == 1 {
        // k = 2 (minimum k)
        (n, m, 2)
    } else if mutation_kind == 2 {
        // k = n (maximum k)
        (n, m, n)
    } else if mutation_kind == 3 {
        // m = 0 (minimum m)
        (n, 0, k)
    } else if mutation_kind == 4 {
        // m = n (maximum m)
        (n, n, k)
    } else if mutation_kind == 5 {
        // n = 1_000_000_000 (max n)
        (1_000_000_000, m, k)
    } else if mutation_kind == 6 {
        // n = 2, k = 2 (minimum valid n and k)
        let m2 = if m <= 2 { m } else { 2i64 };
        (2, m2, 2)
    } else if mutation_kind == 7 {
        // n = k (n equals k)
        let m2 = if m <= k { m } else { k };
        (k, m2, k)
    } else if mutation_kind == 8 && n < 1_000_000_000 {
        // nudge n up
        (n + 1, m, k)
    } else if mutation_kind == 9 && n > 2 && k < n {
        // nudge n down (keep k <= n)
        let m2 = if m < n { m } else { n - 1 };
        (n - 1, m2, k)
    } else if mutation_kind == 10 && k < n {
        // nudge k up
        (n, m, k + 1)
    } else if mutation_kind == 11 && k > 2 {
        // nudge k down
        (n, m, k - 1)
    } else if mutation_kind == 12 && m < n {
        // nudge m up
        (n, m + 1, k)
    } else if mutation_kind == 13 && m > 0 {
        // nudge m down
        (n, m - 1, k)
    } else if mutation_kind == 14 {
        // halve n, clamp k and m
        let hn = if n / 2 >= 2 { n / 2 } else { 2i64 };
        let hk = if k <= hn { k } else { hn };
        let hm = if m <= hn { m } else { hn };
        (hn, hm, hk)
    } else if mutation_kind == 15 {
        // m = n / 2 (medium m)
        (n, n / 2, k)
    } else {
        // fallback: identity
        (n, m, k)
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

fn mutate(seed_n: i64, seed_k: i64, seed_m: i64, mk: u8) -> (i64, i64, i64) {
    let n = seed_n;
    let k = if seed_k <= seed_n { seed_k } else { seed_n };
    let m = if seed_m <= seed_n { seed_m } else { seed_n };
    if mk == 0 {
        (n, m, k)
    } else if mk == 1 {
        (n, m, 2)
    } else if mk == 2 {
        (n, m, n)
    } else if mk == 3 {
        (n, 0, k)
    } else if mk == 4 {
        (n, n, k)
    } else if mk == 5 {
        (1_000_000_000, m, k)
    } else if mk == 6 {
        let m2 = if m <= 2 { m } else { 2 };
        (2, m2, 2)
    } else if mk == 7 {
        let m2 = if m <= k { m } else { k };
        (k, m2, k)
    } else if mk == 8 && n < 1_000_000_000 {
        (n + 1, m, k)
    } else if mk == 9 && n > 2 && k < n {
        let m2 = if m < n { m } else { n - 1 };
        (n - 1, m2, k)
    } else if mk == 10 && k < n {
        (n, m, k + 1)
    } else if mk == 11 && k > 2 {
        (n, m, k - 1)
    } else if mk == 12 && m < n {
        (n, m + 1, k)
    } else if mk == 13 && m > 0 {
        (n, m - 1, k)
    } else if mk == 14 {
        let hn = if n / 2 >= 2 { n / 2 } else { 2 };
        let hk = if k <= hn { k } else { hn };
        let hm = if m <= hn { m } else { hn };
        (hn, hm, hk)
    } else if mk == 15 {
        (n, n / 2, k)
    } else {
        (n, m, k)
    }
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |n: i64, m: i64, k: i64, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if !(2 <= k && k <= n && n <= 1_000_000_000 && 0 <= m && m <= n) { return; }
        let key = format!("{} {} {}", n, m, k);
        if !seen.insert(key) { return; }
        let inp = format!("{} {} {}\n", n, m, k);
        let ans = Solution::min_quiz_score(n, m, k);
        let outs = format!("{}\n", ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    let examples: Vec<(i64, i64, i64)> = vec![(5, 3, 2), (5, 4, 2)];
    for &(n, m, k) in &examples {
        emit(n, m, k, &mut seen, &mut out, &mut count);
    }

    let n_seeds: Vec<i64> = vec![2, 3, 4, 5, 10, 100, 1000, 1_000_000, 1_000_000_000, 999_999_999, 500_000_000];
    let k_seeds: Vec<i64> = vec![2, 3, 4, 5, 10, 100, 1000, 1_000_000, 1_000_000_000];
    let m_seeds: Vec<i64> = vec![0, 1, 2, 3, 5, 10, 100, 1000, 1_000_000, 1_000_000_000];

    let num_mutations: u8 = 16;
    'outer: for &sn in &n_seeds {
        for &sk in &k_seeds {
            for &sm in &m_seeds {
                for mk in 0..num_mutations {
                    if count >= target { break 'outer; }
                    let (n, m, k) = mutate(sn, sk, sm, mk);
                    emit(n, m, k, &mut seen, &mut out, &mut count);
                }
            }
        }
    }

    let mut tries = 0usize;
    while count < target {
        let sn = match tries % 5 {
            0 => rng.gen_range_i64(2, 10),
            1 => rng.gen_range_i64(2, 100),
            2 => rng.gen_range_i64(2, 10_000),
            3 => rng.gen_range_i64(2, 1_000_000),
            _ => rng.gen_range_i64(2, 1_000_000_000),
        };
        let sk = rng.gen_range_i64(2, 1_000_000_000);
        let sm = rng.gen_range_i64(0, 1_000_000_000);
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let (n, m, k) = mutate(sn, sk, sm, mk);
        emit(n, m, k, &mut seen, &mut out, &mut count);
        tries += 1;
        if tries > 100000 { break; }
    }
}

