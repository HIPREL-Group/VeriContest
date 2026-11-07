use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    fillers: &Vec<i64>,
    x_val: i64,
) -> (a: Vec<i64>)
    requires
        1 <= fillers.len() <= 5000,
        0 <= x_val <= 100000,
        forall|i: int| 0 <= i < fillers.len() ==> -100000 <= #[trigger] fillers[i] <= 100000,
    ensures
        1 <= a.len() <= 5000,
        0 <= x_val <= 100000,
        a.len() == fillers.len(),
        forall|i: int| 0 <= i < a.len() ==> -100000 <= #[trigger] a@[i] <= 100000,
{
    let n = fillers.len();
    let mut a: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == fillers.len(),
            0 <= i <= n,
            a.len() == i,
            forall|k: int| 0 <= k < fillers.len() ==> -100000 <= #[trigger] fillers[k] <= 100000,
            forall|k: int| 0 <= k < i as int ==> -100000 <= #[trigger] a@[k] <= 100000,
            forall|k: int| 0 <= k < i as int ==> a@[k] == fillers[k],
        decreases n - i,
    {
        a.push(fillers[i]);
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

fn build_input(cases: &[(Vec<i64>, i64)]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (a, x) in cases {
        s.push_str(&format!("{} {}\n", a.len(), x));
        let parts: Vec<String> = a.iter().map(|v| v.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn build_output(answers: &[Vec<i64>]) -> String {
    let mut s = String::new();
    for ans in answers {
        let parts: Vec<String> = ans.iter().map(|v| v.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn make_test(rng: &mut Rng, mode: usize) -> (Vec<i64>, i64) {
    match mode {
        0 => (vec![rng.gen_range_i64(-100000, 100000)], rng.gen_range_i64(0, 100000)),
        1 => {
            let n = rng.gen_range_usize(1, 50);
            let x = 0;
            ((0..n).map(|_| rng.gen_range_i64(-100, 100)).collect(), x)
        }
        2 => {
            let n = rng.gen_range_usize(1, 50);
            let x = rng.gen_range_i64(1, 100);
            (vec![-100; n], x)
        }
        3 => {
            let n = rng.gen_range_usize(1, 50);
            let x = rng.gen_range_i64(0, 100);
            (vec![100; n], x)
        }
        4 => {
            let n = rng.gen_range_usize(1, 50);
            let x = rng.gen_range_i64(0, 100);
            (vec![0; n], x)
        }
        5 => {
            let n = rng.gen_range_usize(1, 100);
            let x = rng.gen_range_i64(0, 100000);
            ((0..n).map(|_| rng.gen_range_i64(-100, 100)).collect(), x)
        }
        6 => {
            let n = 200;
            let x = rng.gen_range_i64(0, 100);
            ((0..n).map(|_| rng.gen_range_i64(-100, 100)).collect(), x)
        }
        7 => {
            let n = rng.gen_range_usize(1, 50);
            let x = 100000;
            ((0..n).map(|_| rng.gen_range_i64(-100000, 100000)).collect(), x)
        }
        8 => {
            // alternating
            let n = rng.gen_range_usize(1, 50);
            let x = rng.gen_range_i64(0, 100);
            ((0..n).map(|i| if i % 2 == 0 { -100 } else { 100 }).collect(), x)
        }
        9 => {
            let n = rng.gen_range_usize(1, 50);
            let x = rng.gen_range_i64(0, 100);
            ((0..n).map(|_| rng.gen_range_i64(-100, 100)).collect(), x)
        }
        _ => {
            let n = rng.gen_range_usize(1, 100);
            let x = rng.gen_range_i64(0, 100);
            ((0..n).map(|_| rng.gen_range_i64(-100, 100)).collect(), x)
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
        let t: usize = if count < 10 { 1 } else { rng.gen_range_usize(1, 5) };
        let mut cases: Vec<(Vec<i64>, i64)> = Vec::new();
        for _ in 0..t {
            let mode = idx % modes;
            idx += 1;
            cases.push(make_test(&mut rng, mode));
        }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<Vec<i64>> = cases.iter().map(|(a, x)| Solution::increase_subarray_sums(a.clone(), *x)).collect();
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

