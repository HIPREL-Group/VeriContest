use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n_seed: i32,
    k_seed: i32,
    d_raw: i32,
    mutation_kind: u8,
) -> (result: (i32, i32, i32))
    requires
        1 <= n_seed <= 100,
        1 <= k_seed <= 100,
        1 <= d_raw <= 100,
    ensures
        1 <= result.0 <= 100,
        1 <= result.2 <= result.1 <= 100,
{
    let base_d: i32 = if d_raw <= k_seed { d_raw } else { k_seed };

    if mutation_kind == 0 {
        // identity
        (n_seed, k_seed, base_d)
    } else if mutation_kind == 1 {
        // n = 1 (min boundary)
        (1, k_seed, base_d)
    } else if mutation_kind == 2 {
        // n = 100 (max boundary)
        (100, k_seed, base_d)
    } else if mutation_kind == 3 {
        // d = k (edge: minimum gap)
        (n_seed, k_seed, k_seed)
    } else if mutation_kind == 4 {
        // d = 1 (minimum d)
        (n_seed, k_seed, 1)
    } else if mutation_kind == 5 {
        // all max
        (100, 100, 100)
    } else if mutation_kind == 6 {
        // all min
        (1, 1, 1)
    } else if mutation_kind == 7 && n_seed < 100 {
        // nudge n up
        (n_seed + 1, k_seed, base_d)
    } else if mutation_kind == 8 && n_seed > 1 {
        // nudge n down
        (n_seed - 1, k_seed, base_d)
    } else if mutation_kind == 9 && k_seed < 100 {
        // nudge k up, keep d valid
        (n_seed, k_seed + 1, base_d)
    } else if mutation_kind == 10 && k_seed > 1 && base_d < k_seed {
        // nudge k down (only if d < k so d <= k-1 holds)
        (n_seed, k_seed - 1, base_d)
    } else if mutation_kind == 11 {
        // k = 1, d = 1
        (n_seed, 1, 1)
    } else if mutation_kind == 12 {
        // k = 100, keep d
        let d2: i32 = if d_raw <= 100 { d_raw } else { 100 };
        (n_seed, 100, d2)
    } else {
        // fallback: identity
        (n_seed, k_seed, base_d)
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
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let r = (hi as i64 - lo as i64 + 1) as u64;
        (lo as i64 + (self.next_u64() % r) as i64) as i32
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

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |n: i32, k: i32, d: i32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if !(1 <= n && n <= 100 && 1 <= k && k <= 100 && 1 <= d && d <= k) { return; }
        let key = format!("{} {} {}", n, k, d);
        if !seen.insert(key) { return; }
        let inp = format!("{} {} {}\n", n, k, d);
        let ans = Solution::count_k_tree_paths(n, k, d);
        let outs = format!("{}\n", ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    // examples
    emit(3, 3, 2, &mut seen, &mut out, &mut count);
    emit(3, 3, 3, &mut seen, &mut out, &mut count);
    emit(4, 3, 2, &mut seen, &mut out, &mut count);
    emit(4, 5, 2, &mut seen, &mut out, &mut count);

    // boundaries
    for n in [1, 2, 50, 99, 100].iter() {
        for k in [1, 2, 50, 99, 100].iter() {
            for d in [1, *k / 2, *k].iter() {
                if *d >= 1 && *d <= *k {
                    emit(*n, *k, *d, &mut seen, &mut out, &mut count);
                }
            }
        }
    }

    while count < target {
        let n = rng.gen_range_i32(1, 100);
        let k = rng.gen_range_i32(1, 100);
        let d = rng.gen_range_i32(1, k);
        emit(n, k, d, &mut seen, &mut out, &mut count);
    }
}

