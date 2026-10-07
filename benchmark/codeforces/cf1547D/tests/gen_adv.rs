use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    raw: &Vec<u32>,
) -> (result: (usize, Vec<u32>))
    requires
        1 <= n <= 200000,
        raw.len() == n,
    ensures
        result.0 == n,
        1 <= result.0 <= 200000,
        result.1.len() == n,
        forall|i: int| 0 <= i < n ==> #[trigger] result.1[i] < 1073741824u32,
{
    let mut x: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            x.len() == i,
            raw.len() == n,
            forall|k: int| 0 <= k < i as int ==> #[trigger] x[k] < 1073741824u32,
        decreases n - i,
    {
        let v = raw[i] % 1073741824u32;
        assert(v < 1073741824u32);
        x.push(v);
        i = i + 1;
    }
    (n, x)
}

}

use std::io::Write;
use std::collections::HashSet;

struct Rng { state: u64 }
impl Rng {
    fn new(seed: u64) -> Self { Self { state: seed.wrapping_add(1) } }
    fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.state
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn gen_u32(&mut self) -> u32 {
        (self.next_u64() as u32) & 0x3FFFFFFF
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

fn build_input(cases: &[(usize, Vec<u32>)]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (n, x) in cases {
        s.push_str(&format!("{}\n", n));
        let parts: Vec<String> = x.iter().map(|v| v.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn build_output(answers: &[Vec<u32>]) -> String {
    let mut s = String::new();
    for y in answers {
        let parts: Vec<String> = y.iter().map(|v| v.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn gen_mode(rng: &mut Rng, mode: usize) -> (usize, Vec<u32>) {
    match mode {
        0 => { let v = rng.gen_u32(); (1, vec![v]) }
        1 => { let n = rng.gen_range_usize(1, 50); (n, vec![0u32; n]) }
        2 => { let n = rng.gen_range_usize(1, 100); let v = rng.gen_u32(); (n, vec![v; n]) }
        3 => {
            let n = 30;
            let mut v = Vec::new();
            for i in 0..n { v.push(1u32 << i); }
            (n, v)
        }
        4 => {
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::new();
            let mut cur: u32 = 0;
            for _ in 0..n {
                cur |= rng.gen_u32() & 0x3FFFFFFF;
                v.push(cur);
            }
            (n, v)
        }
        5 => {
            let n = rng.gen_range_usize(1, 30);
            let mut v = Vec::new();
            let mut cur: u32 = 0x3FFFFFFF;
            for _ in 0..n {
                v.push(cur);
                cur = cur >> 1;
            }
            (n, v)
        }
        6 => { let n = rng.gen_range_usize(1, 20); (n, vec![0x3FFFFFFFu32; n]) }
        7 => {
            let n = rng.gen_range_usize(2, 50);
            let mut v = Vec::new();
            for i in 0..n {
                if i % 2 == 0 { v.push(0u32); } else { v.push(0x3FFFFFFFu32); }
            }
            (n, v)
        }
        8 => {
            let n = rng.gen_range_usize(500, 2000);
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_u32()); }
            (n, v)
        }
        9 => {
            let n = rng.gen_range_usize(1, 30);
            let mut v = Vec::new();
            for i in 0..n { v.push(1u32 << (i % 30)); }
            (n, v)
        }
        _ => {
            let n = rng.gen_range_usize(1, 200);
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_u32()); }
            (n, v)
        }
    }
}

fn main() {
    let mut rng = Rng::new(1);
    let modes = 11usize;
    let total = 200usize;

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut seen: HashSet<String> = HashSet::new();
    let mut count = 0usize;
    let mut idx = 0usize;
    while count < total {
        let t: usize = if count < 10 { 1 } else { rng.gen_range_usize(1, 20) };
        let mut cases: Vec<(usize, Vec<u32>)> = Vec::new();
        for _ in 0..t {
            let mode = idx % modes;
            idx += 1;
            let (n, vals) = gen_mode(&mut rng, mode);
            cases.push((n, vals));
        }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<Vec<u32>> = cases.iter().map(|(n, x)| Solution::co_growing(*n, x.clone())).collect();
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

