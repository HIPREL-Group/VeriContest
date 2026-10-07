use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_n: i128, seed_k: i128, mutation_kind: u8)
    -> (result: (i128, i128))
    requires
        1 <= seed_n <= 1_000_000_000_000_000_000,
        2 <= seed_k <= 1_000_000_000,
    ensures
        1 <= result.0 <= 1_000_000_000_000_000_000,
        2 <= result.1 <= 1_000_000_000,
{
    let mut n = seed_n;
    let mut k = seed_k;

    if mutation_kind == 0 {
        // identity
    } else if mutation_kind == 1 && n < 1_000_000_000_000_000_000 {
        n = n + 1;                                   // nudge n up
    } else if mutation_kind == 2 && n > 1 {
        n = n - 1;                                   // nudge n down
    } else if mutation_kind == 3 && k < 1_000_000_000 {
        k = k + 1;                                   // nudge k up
    } else if mutation_kind == 4 && k > 2 {
        k = k - 1;                                   // nudge k down
    } else if mutation_kind == 5 {
        n = 1;                                       // min n (special case: 0 splitters)
    } else if mutation_kind == 6 {
        n = 1_000_000_000_000_000_000;               // max n
    } else if mutation_kind == 7 {
        k = 2;                                       // min k
    } else if mutation_kind == 8 {
        k = 1_000_000_000;                           // max k
    } else if mutation_kind == 9 {
        if n <= 500_000_000_000_000_000 {
            n = n * 2;                               // double n
        }
    } else if mutation_kind == 10 {
        n = n / 2 + 1;                               // halve n (stay >= 1)
    } else if mutation_kind == 11 {
        if k <= 500_000_000 {
            k = k * 2;                               // double k
        }
    } else if mutation_kind == 12 {
        k = k / 2 + 1;                               // halve k (stay >= 2)
        if k < 2 { k = 2; }
    } else if mutation_kind == 13 {
        n = seed_k as i128;                          // n = k (small n)
        if n < 1 { n = 1; }
    } else if mutation_kind == 14 {
        n = 2;                                       // n = 2 (smallest non-trivial)
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
    fn gen_range_i128(&mut self, lo: i128, hi: i128) -> i128 {
        let r = (hi - lo + 1) as u128;
        let v = ((self.next_u64() as u128) ^ ((self.next_u64() as u128) << 32)) % r;
        lo + v as i128
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

fn mutate(seed_n: i128, seed_k: i128, mk: u8) -> (i128, i128) {
    let mut n = seed_n;
    let mut k = seed_k;
    if mk == 0 {
    } else if mk == 1 && n < 1_000_000_000_000_000_000 {
        n = n + 1;
    } else if mk == 2 && n > 1 {
        n = n - 1;
    } else if mk == 3 && k < 1_000_000_000 {
        k = k + 1;
    } else if mk == 4 && k > 2 {
        k = k - 1;
    } else if mk == 5 {
        n = 1;
    } else if mk == 6 {
        n = 1_000_000_000_000_000_000;
    } else if mk == 7 {
        k = 2;
    } else if mk == 8 {
        k = 1_000_000_000;
    } else if mk == 9 && n <= 500_000_000_000_000_000 {
        n = n * 2;
    } else if mk == 10 {
        n = n / 2 + 1;
    } else if mk == 11 && k <= 500_000_000 {
        k = k * 2;
    } else if mk == 12 {
        k = k / 2 + 1;
        if k < 2 { k = 2; }
    } else if mk == 13 {
        n = seed_k;
        if n < 1 { n = 1; }
    } else if mk == 14 {
        n = 2;
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

    let mut emit = |n: i128, k: i128, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if !(1 <= n && n <= 1_000_000_000_000_000_000 && 2 <= k && k <= 1_000_000_000) { return; }
        let key = format!("{} {}", n, k);
        if !seen.insert(key) { return; }
        let inp = format!("{} {}\n", n, k);
        let ans = Solution::min_splitters(n, k);
        let outs = format!("{}\n", ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    let examples: [(i128, i128); 3] = [(4, 3), (5, 5), (8, 4)];
    for &(n, k) in &examples {
        emit(n, k, &mut seen, &mut out, &mut count);
    }

    let num_mutations: u8 = 15;
    let mut generated = 0usize;
    while count < target {
        let (sn, sk) = match generated % 6 {
            0 => (rng.gen_range_i128(1, 10), rng.gen_range_i128(2, 10)),
            1 => (rng.gen_range_i128(1, 1000), rng.gen_range_i128(2, 1000)),
            2 => (rng.gen_range_i128(1, 1_000_000), rng.gen_range_i128(2, 1_000_000)),
            3 => (rng.gen_range_i128(1_000_000, 1_000_000_000_000), rng.gen_range_i128(1_000, 1_000_000_000)),
            4 => (rng.gen_range_i128(1, 1_000_000_000_000_000_000), rng.gen_range_i128(2, 1_000_000_000)),
            _ => {
                let n_bounds: [i128; 5] = [1, 2, 1_000_000_000, 1_000_000_000_000_000_000, 999_999_999_999_999_999];
                let k_bounds: [i128; 5] = [2, 3, 1_000_000_000, 999_999_999, 500_000_000];
                (n_bounds[(rng.next_u64() as usize) % 5], k_bounds[(rng.next_u64() as usize) % 5])
            }
        };
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let (n, k) = mutate(sn, sk, mk);
        emit(n, k, &mut seen, &mut out, &mut count);
        generated += 1;
        if generated > 100000 { break; }
    }
}

