use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (a: Vec<i32>)
    requires
        2 <= values.len() <= 100,
        forall|t: int| #![trigger values[t]] 0 <= t < values.len() ==> 0 <= (values[t] as int) <= 100,
    ensures
        2 <= a.len() <= 100,
        forall|t: int| #![trigger a[t]] 0 <= t < a.len() ==> 0 <= (a[t] as int) <= 100,
{
    let mut a: Vec<i32> = Vec::new();
    let n = values.len();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == values.len(),
            a.len() == i,
            forall|k: int| #![trigger a[k]] 0 <= k < i as int ==> 0 <= (a[k] as int) <= 100,
            forall|t: int| #![trigger values[t]] 0 <= t < values.len() ==> 0 <= (values[t] as int) <= 100,
        decreases n - i,
    {
        let v = values[i];
        assert(0 <= (v as int) <= 100);
        a.push(v);
        i = i + 1;
    }
    a
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

fn build_input(cases: &[Vec<i32>]) -> String {
    let mut s = format!("{}\n", cases.len());
    for a in cases {
        s.push_str(&format!("{}\n", a.len()));
        let parts: Vec<String> = a.iter().map(|v| v.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn build_output(answers: &[i32]) -> String {
    let mut s = String::new();
    for &a in answers { s.push_str(&format!("{}\n", a)); }
    s
}

fn make_test(rng: &mut Rng, mode: usize) -> Vec<i32> {
    match mode {
        0 => vec![0; 2],
        1 => vec![rng.gen_range_i64(1, 100) as i32; 2],
        2 => {
            let n = rng.gen_range_usize(2, 100);
            vec![0; n]
        }
        3 => {
            // All distinct positive
            let n = rng.gen_range_usize(2, 50);
            (1..=n as i32).collect()
        }
        4 => {
            // All same positive
            let n = rng.gen_range_usize(2, 100);
            let v = rng.gen_range_i64(1, 100) as i32;
            vec![v; n]
        }
        5 => {
            // One zero
            let n = rng.gen_range_usize(2, 100);
            let mut v: Vec<i32> = (0..n).map(|_| rng.gen_range_i64(0, 100) as i32).collect();
            v[0] = 0;
            v
        }
        6 => {
            // 100 elements
            let n = 100;
            (0..n).map(|_| rng.gen_range_i64(0, 100) as i32).collect()
        }
        7 => {
            let n = rng.gen_range_usize(2, 100);
            (0..n).map(|_| rng.gen_range_i64(0, 5) as i32).collect()
        }
        8 => {
            let n = rng.gen_range_usize(2, 100);
            (0..n).map(|_| rng.gen_range_i64(0, 100) as i32).collect()
        }
        9 => {
            // No zeros, all distinct
            let n = rng.gen_range_usize(2, 50);
            (0..n).map(|i| (i + 1) as i32).collect()
        }
        _ => {
            let n = rng.gen_range_usize(2, 100);
            (0..n).map(|_| rng.gen_range_i64(0, 100) as i32).collect()
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
        let mut cases: Vec<Vec<i32>> = Vec::new();
        for _ in 0..t {
            let mode = idx % modes;
            idx += 1;
            cases.push(make_test(&mut rng, mode));
        }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<i32> = cases.iter().map(|a| Solution::min_ops_to_all_zero(a.clone())).collect();
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

