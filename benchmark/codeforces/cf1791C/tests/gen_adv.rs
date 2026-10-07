use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: usize, bits: &Vec<i64>) -> (result: (usize, Vec<i64>))
    requires
        n >= 1,
        n <= 2000,
        bits.len() == n,
        forall|i: int| 0 <= i < n as int ==> (#[trigger] bits@[i] == 0 || bits@[i] == 1),
    ensures
        result.0 == n,
        result.0 >= 1,
        result.1.len() == result.0,
        forall|i: int| 0 <= i < result.0 as int ==> (#[trigger] result.1@[i] == 0 || result.1@[i] == 1),
{
    let mut out: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == bits.len(),
            0 <= i <= n,
            out.len() == i,
            forall|k: int| 0 <= k < i as int ==> (#[trigger] out@[k] == 0 || out@[k] == 1),
            forall|k: int| 0 <= k < i as int ==> out@[k] == bits@[k],
            forall|k: int| 0 <= k < n as int ==> (#[trigger] bits@[k] == 0 || bits@[k] == 1),
        decreases n - i,
    {
        let b = bits[i];
        out.push(b);
        i = i + 1;
    }
    (n, out)
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

type TC = (usize, String);

fn build_input(cases: &[TC]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (n, st) in cases {
        s.push_str(&format!("{}\n{}\n", n, st));
    }
    s
}

fn build_output(cases: &[TC]) -> String {
    let mut s = String::new();
    for (n, st) in cases {
        let v: Vec<i64> = st.as_bytes().iter().map(|&b| (b - b'0') as i64).collect();
        let ans = Solution::shortest_original(*n, v);
        s.push_str(&format!("{}\n", ans));
    }
    s
}

fn gen_case(rng: &mut Rng, mode: usize) -> TC {
    match mode {
        0 => {
            // n=1
            let s = if rng.next_u64() % 2 == 0 { "0" } else { "1" };
            (1, s.to_string())
        }
        1 => {
            // all 0s
            let n = rng.gen_range_usize(1, 100);
            (n, "0".repeat(n))
        }
        2 => {
            // all 1s
            let n = rng.gen_range_usize(1, 100);
            (n, "1".repeat(n))
        }
        3 => {
            // alternating starting with 0
            let n = rng.gen_range_usize(2, 100);
            let s: String = (0..n).map(|i| if i % 2 == 0 { '0' } else { '1' }).collect();
            (n, s)
        }
        4 => {
            // 0...01...1 (palindrome of 0/1 — could be reducible)
            let n = rng.gen_range_usize(2, 100);
            let mid = n / 2;
            let s: String = (0..n).map(|i| if i < mid { '0' } else { '1' }).collect();
            (n, s)
        }
        5 => {
            // moderate-large random
            let n = rng.gen_range_usize(500, 2000);
            let s: String = (0..n).map(|_| if rng.next_u64() % 2 == 0 { '0' } else { '1' }).collect();
            (n, s)
        }
        _ => {
            let n = rng.gen_range_usize(1, 200);
            let s: String = (0..n).map(|_| if rng.next_u64() % 2 == 0 { '0' } else { '1' }).collect();
            (n, s)
        }
    }
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(1791);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;
    let mut tries = 0usize;

    while count < target && tries < 100000 {
        tries += 1;
        let t: usize = if count % 5 == 0 { rng.gen_range_usize(2, 30) } else { 1 };
        let mut cases: Vec<TC> = Vec::new();
        for _ in 0..t {
            let mode = (rng.next_u64() as usize) % 7;
            cases.push(gen_case(&mut rng, mode));
        }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let outs = build_output(&cases);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}

