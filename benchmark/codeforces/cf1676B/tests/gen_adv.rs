use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: Vec<i64>) -> (result: Vec<i64>)
    ensures
        1 <= result.len() <= 50,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 10000000,
{
    let n = if values.len() < 1 { 1usize }
            else if values.len() > 50 { 50usize } else { values.len() };
    let limit = 10000000;
    let mut result = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant
            1 <= n <= 50,
            limit == 10000000,
            0 <= i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < result.len() ==> 1 <= #[trigger] result[j] <= limit,
        decreases n - i,
    {
        let value = if i < values.len() { values[i] } else { 1 };
        let value = if value < 1 { 1 } else if value > limit { limit } else { value };
        result.push(value);
        i += 1;
    }
    result
}


pub fn generate_candidate(values: &Vec<i64>) -> (result: Vec<i64>)
    requires
        1 <= values.len() <= 50,
        forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 1_000_000_000,
    ensures
        1 <= result.len() <= 50,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] as int <= 1_000_000_000,
{
    let n = values.len();
    let mut out: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            0 <= i <= n,
            out.len() == i,
            forall|k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 1_000_000_000,
            forall|k: int| 0 <= k < i as int ==> #[trigger] out[k] == values[k],
        decreases n - i,
    {
        out.push(values[i]);
        i = i + 1;
    }
    out
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
        let x = self.next_u64();
        let v = ((x >> 32) ^ x) as u128;
        (lo as i128 + (v % r) as i128) as i64
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let x = self.next_u64();
        let v = ((x >> 32) ^ x) as usize;
        lo + v % (hi - lo + 1)
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

fn build_input(cases: &[Vec<i64>]) -> String {
    let mut s = format!("{}\n", cases.len());
    for a in cases {
        s.push_str(&format!("{}\n", a.len()));
        let parts: Vec<String> = a.iter().map(|v| v.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn build_output(answers: &[i64]) -> String {
    let mut s = String::new();
    for &a in answers { s.push_str(&format!("{}\n", a)); }
    s
}

fn make_test(rng: &mut Rng, mode: usize) -> Vec<i64> {
    match mode {
        0 => vec![rng.gen_range_i64(1, 1_000_000_000)],
        1 => {
            let n = rng.gen_range_usize(1, 50);
            let v = rng.gen_range_i64(1, 1_000_000);
            vec![v; n]
        }
        2 => {
            let n = rng.gen_range_usize(1, 50);
            (0..n).map(|i| (i as i64) + 1).collect()
        }
        3 => {
            let n = 50;
            (0..n).map(|_| rng.gen_range_i64(1, 1_000_000_000)).collect()
        }
        4 => {
            let n = rng.gen_range_usize(1, 50);
            (0..n).map(|_| rng.gen_range_i64(1, 1_000_000_000)).collect()
        }
        5 => {
            // 1 and 1_000_000_000 alternating
            let n = rng.gen_range_usize(2, 50);
            (0..n).map(|i| if i % 2 == 0 { 1 } else { 1_000_000_000 }).collect()
        }
        6 => {
            let n = rng.gen_range_usize(1, 50);
            vec![1; n]
        }
        7 => {
            let n = rng.gen_range_usize(1, 50);
            vec![1_000_000_000; n]
        }
        8 => {
            let n = rng.gen_range_usize(2, 50);
            let mut v: Vec<i64> = (0..n).map(|_| rng.gen_range_i64(1, 1_000_000)).collect();
            v[0] = 1;
            v
        }
        9 => {
            let n = rng.gen_range_usize(1, 50);
            (0..n).map(|_| rng.gen_range_i64(1, 100)).collect()
        }
        _ => {
            let n = rng.gen_range_usize(1, 50);
            (0..n).map(|_| rng.gen_range_i64(1, 1_000_000_000)).collect()
        }
    }
}

fn main() {
    let mut rng = Rng::new(1);
    let modes = 10usize;
    let total = 200usize;

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut seen: HashSet<String> = HashSet::new();
    let mut count = 0usize;
    let mut idx = 0;
    while count < total {
        let t: usize = if count < 10 { 1 } else { rng.gen_range_usize(1, 10) };
        let mut cases: Vec<Vec<i64>> = Vec::new();
        for _ in 0..t {
            let mode = idx % modes;
            idx += 1;
            cases.push(make_test(&mut rng, mode));
        }
        let cases: Vec<_> = cases.iter().cloned().map(generate_test_case).collect();
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<i64> = cases.iter().map(|a| Solution::min_operations_to_equal(a.clone())).collect();
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}
