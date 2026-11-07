use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_n: u64, seed_k: u64, mutation_kind: u8)
    -> (result: (u64, u64))
    requires
        1 <= seed_k <= seed_n,
        seed_n <= 1_000_000_000_000u64,
    ensures
        1 <= result.1 <= result.0,
        result.0 <= 1_000_000_000_000u64,
{
    let mut n = seed_n;
    let mut k = seed_k;

    if mutation_kind == 0 {
        // identity
    } else if mutation_kind == 1 && n < 1_000_000_000_000 {
        n = n + 1;                           // nudge n up (k <= n still holds)
    } else if mutation_kind == 2 && k > 1 {
        k = k - 1;                           // nudge k down
    } else if mutation_kind == 3 {
        k = 1;                               // min k
    } else if mutation_kind == 4 {
        k = n;                               // max k = n
    } else if mutation_kind == 5 {
        n = 1;
        k = 1;                               // minimal case
    } else if mutation_kind == 6 {
        n = 1_000_000_000_000;
        k = 1;                               // max n, min k
    } else if mutation_kind == 7 {
        n = 1_000_000_000_000;
        k = 1_000_000_000_000;               // max n, max k
    } else if mutation_kind == 8 && k < n {
        k = k + 1;                           // nudge k up
    } else if mutation_kind == 9 && n > 1 && k < n {
        n = n - 1;                           // nudge n down (keep k <= n)
    } else if mutation_kind == 10 {
        // halve both
        n = n / 2 + 1;
        k = if k / 2 + 1 <= n / 2 + 1 { k / 2 + 1 } else { n / 2 + 1 };
    } else if mutation_kind == 11 && n <= 500_000_000_000 {
        n = n * 2;                           // double n
    } else if mutation_kind == 12 {
        // k at midpoint
        let mid = (n + 1) / 2;
        k = mid;
    } else {
        // fallback: identity
    }

    (n, k)
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
    fn gen_range_u64(&mut self, lo: u64, hi: u64) -> u64 {
        let r = (hi as u128 - lo as u128 + 1) as u128;
        (lo as u128 + (self.next_u64() as u128) % r) as u64
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

fn mutate(seed_n: u64, seed_k: u64, mk: u8) -> (u64, u64) {
    let mut n = seed_n;
    let mut k = seed_k;
    if mk == 0 {
    } else if mk == 1 && n < 1_000_000_000_000 {
        n = n + 1;
    } else if mk == 2 && k > 1 {
        k = k - 1;
    } else if mk == 3 {
        k = 1;
    } else if mk == 4 {
        k = n;
    } else if mk == 5 {
        n = 1; k = 1;
    } else if mk == 6 {
        n = 1_000_000_000_000; k = 1;
    } else if mk == 7 {
        n = 1_000_000_000_000; k = 1_000_000_000_000;
    } else if mk == 8 && k < n {
        k = k + 1;
    } else if mk == 9 && n > 1 && k < n {
        n = n - 1;
    } else if mk == 10 {
        n = n / 2 + 1;
        let knew = k / 2 + 1;
        k = if knew <= n { knew } else { n };
    } else if mk == 11 && n <= 500_000_000_000 {
        n = n * 2;
    } else if mk == 12 {
        let mid = (n + 1) / 2;
        k = mid;
    }
    (n, k)
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |n: u64, k: u64, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if !(1 <= k && k <= n && n <= 1_000_000_000_000) { return; }
        let key = format!("{} {}", n, k);
        if !seen.insert(key) { return; }
        let inp = format!("{} {}\n", n, k);
        let ans = Solution::kth_even_odds(n, k);
        let outs = format!("{}\n", ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    emit(10, 3, &mut seen, &mut out, &mut count);
    emit(7, 7, &mut seen, &mut out, &mut count);

    let num_mutations: u8 = 13;
    let mut generated = 0usize;
    while count < target {
        let n: u64 = match generated % 5 {
            0 => rng.gen_range_u64(1, 5),
            1 => rng.gen_range_u64(1, 100),
            2 => rng.gen_range_u64(100, 10_000),
            3 => rng.gen_range_u64(10_000, 1_000_000_000),
            _ => rng.gen_range_u64(1_000_000_000, 1_000_000_000_000),
        };
        let k: u64 = rng.gen_range_u64(1, n);
        let mk = (generated % num_mutations as usize) as u8;
        let (rn, rk) = mutate(n, k, mk);
        emit(rn, rk, &mut seen, &mut out, &mut count);
        generated += 1;
        if generated > 100000 { break; }
    }
}

