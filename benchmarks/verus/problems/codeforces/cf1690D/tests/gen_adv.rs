use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    k: usize,
    bits: &Vec<u8>,
) -> (result: (usize, usize, Vec<i64>))
    requires
        1 <= n <= 200000,
        1 <= k <= n,
        bits.len() == n,
        forall|i: int| 0 <= i < n as int ==> (#[trigger] bits[i] == 0u8 || bits[i] == 1u8),
    ensures
        result.0 == n,
        result.1 == k,
        1 <= result.0 <= 200000,
        1 <= result.1 <= result.0,
        result.2.len() == result.0,
        forall|i: int| 0 <= i < result.0 as int ==> (#[trigger] result.2@[i] == 0 || result.2@[i] == 1),
{
    let mut s: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == bits.len(),
            0 <= i <= n,
            s.len() == i,
            forall|j: int| 0 <= j < n as int ==> (#[trigger] bits[j] == 0u8 || bits[j] == 1u8),
            forall|j: int| 0 <= j < i as int ==> (#[trigger] s@[j] == 0 || s@[j] == 1),
        decreases n - i,
    {
        let v: i64 = if bits[i] == 1u8 { 1 } else { 0 };
        s.push(v);
        i = i + 1;
    }
    (n, k, s)
}

}

use std::io::Write;
use std::collections::HashSet;

struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self { Self(seed.wrapping_add(1)) }
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

fn cells_to_string(cells: &[i64]) -> String {
    let mut s = String::with_capacity(cells.len());
    for &c in cells {
        if c == 1 { s.push('W'); } else { s.push('B'); }
    }
    s
}

fn build_input(cases: &[(usize, usize, Vec<i64>)]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (n, k, cells) in cases {
        s.push_str(&format!("{} {}\n", n, k));
        s.push_str(&cells_to_string(cells));
        s.push('\n');
    }
    s
}

fn build_output(answers: &[usize]) -> String {
    let mut s = String::new();
    for a in answers {
        s.push_str(&format!("{}\n", a));
    }
    s
}

fn build_random(rng: &mut Rng, n: usize, p_white: u32) -> Vec<i64> {
    (0..n).map(|_| {
        let r = (rng.next_u64() % 100) as u32;
        if r < p_white { 1i64 } else { 0i64 }
    }).collect()
}

fn build_all(n: usize, val: i64) -> Vec<i64> {
    vec![val; n]
}

fn build_alternating(n: usize, start: i64) -> Vec<i64> {
    (0..n).map(|i| if i % 2 == 0 { start } else { 1 - start }).collect()
}

fn build_block(n: usize, black_start: usize, black_len: usize) -> Vec<i64> {
    let mut v = vec![1i64; n];
    let end = (black_start + black_len).min(n);
    for i in black_start..end { v[i] = 0; }
    v
}

fn gen_one(rng: &mut Rng, mode: usize) -> (usize, usize, Vec<i64>) {
    match mode {
        0 => {
            let n = rng.gen_range_usize(1, 10);
            let k = rng.gen_range_usize(1, n);
            (n, k, build_random(rng, n, 50))
        }
        1 => {
            let n = rng.gen_range_usize(1, 1000);
            let k = rng.gen_range_usize(1, n);
            (n, k, build_all(n, 1))
        }
        2 => {
            let n = rng.gen_range_usize(1, 1000);
            let k = rng.gen_range_usize(1, n);
            (n, k, build_all(n, 0))
        }
        3 => {
            let n = rng.gen_range_usize(1, 500);
            (n, n, build_random(rng, n, 30))
        }
        4 => {
            let n = rng.gen_range_usize(1, 500);
            (n, 1, build_random(rng, n, 70))
        }
        5 => {
            let n = rng.gen_range_usize(2, 500);
            let k = rng.gen_range_usize(1, n);
            let start = (rng.next_u64() % 2) as i64;
            (n, k, build_alternating(n, start))
        }
        6 => {
            let n = rng.gen_range_usize(5, 500);
            let k = rng.gen_range_usize(1, n);
            let blen = rng.gen_range_usize(1, n);
            let bstart = if n - blen == 0 { 0 } else { rng.gen_range_usize(0, n - blen) };
            (n, k, build_block(n, bstart, blen))
        }
        7 => {
            // moderate-large to keep total size reasonable
            let n = 2000usize;
            let k = rng.gen_range_usize(1, n);
            (n, k, build_random(rng, n, 40))
        }
        8 => {
            let bits = if rng.next_u64() % 2 == 0 { vec![0i64] } else { vec![1i64] };
            (1, 1, bits)
        }
        _ => {
            let n = rng.gen_range_usize(1000, 5000);
            let k = rng.gen_range_usize(1, n);
            (n, k, build_random(rng, n, 90))
        }
    }
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(1690);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;
    let mut tries = 0usize;

    while count < target && tries < 100000 {
        tries += 1;
        // Mostly single-case bundles to ensure stress on individual cases, with some multi-test
        let t: usize = if count % 5 == 0 { rng.gen_range_usize(2, 20) } else { 1 };
        let mut cases: Vec<(usize, usize, Vec<i64>)> = Vec::new();
        let mut answers: Vec<usize> = Vec::new();
        for _ in 0..t {
            let mode = (rng.next_u64() as usize) % 10;
            let (n, k, cells) = gen_one(&mut rng, mode);
            let ans = Solution::min_recolors(n, k, cells.clone());
            cases.push((n, k, cells));
            answers.push(ans);
        }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}

