use vstd::prelude::*;

verus! {

pub fn generate_test_case(n_val: i128, k_val: i128) -> (res: (i128, i128))
    requires
        1 <= n_val <= 1_000_000_000_000_000_000,
        2 <= k_val <= 1_000_000_000,
    ensures
        ({
            let (n, k) = res;
            1 <= n <= 1_000_000_000_000_000_000 && 2 <= k <= 1_000_000_000
        }),
{
    (n_val, k_val)
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

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(1);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |n: i128, k: i128, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| -> bool {
        if *count >= target { return false; }
        if !(1 <= n && n <= 1_000_000_000_000_000_000 && 2 <= k && k <= 1_000_000_000) { return false; }
        let key = format!("{} {}", n, k);
        if !seen.insert(key) { return false; }
        let inp = format!("{} {}\n", n, k);
        let ans = Solution::min_splitters(n, k);
        let outs = format!("{}\n", ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
        true
    };

    // Hand-crafted adversarial cases
    let cases: Vec<(i128, i128)> = vec![
        (1, 2), (1, 1_000_000_000), (1, 3),
        (2, 2), (2, 1_000_000_000), (3, 2), (3, 3), (4, 3), (5, 5), (8, 4),
        (1_000_000_000_000_000_000, 2),
        (1_000_000_000_000_000_000, 3),
        (1_000_000_000_000_000_000, 1_000_000_000),
        (1_000_000_000, 1_000_000_000),
        (999_999_999, 1_000_000_000),
        (499_501, 1000),
        (499_500, 1000),
        (499_502, 1000),
        (1_000_000_001, 1_000_000_000),
        (6, 5),
        (4, 5),
    ];
    for (n, k) in cases {
        emit(n, k, &mut seen, &mut out, &mut count);
    }

    // Random cases
    while count < target {
        let mode = (rng.next_u64() % 4) as u32;
        let (n, k) = match mode {
            0 => (rng.gen_range_i128(1, 1_000_000_000_000_000_000), rng.gen_range_i128(2, 1_000_000_000)),
            1 => (rng.gen_range_i128(1, 1000), rng.gen_range_i128(2, 100)),
            2 => (rng.gen_range_i128(1, 1_000_000_000), rng.gen_range_i128(2, 1_000_000_000)),
            _ => (rng.gen_range_i128(1_000_000_000_000, 1_000_000_000_000_000_000), rng.gen_range_i128(2, 1_000_000)),
        };
        emit(n, k, &mut seen, &mut out, &mut count);
    }
}

