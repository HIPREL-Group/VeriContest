use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: usize, a_vals: &Vec<i32>, b_vals: &Vec<i32>) -> (result: (Vec<i32>, Vec<i32>))
    requires
        1 <= n <= 100,
        a_vals.len() == n,
        b_vals.len() == n,
        forall|i: int| 0 <= i < n ==> -100 <= #[trigger] a_vals[i] <= 100,
        forall|i: int| 0 <= i < n ==> -100 <= #[trigger] b_vals[i] <= 100,
    ensures
        1 <= result.0.len() <= 100,
        result.0.len() == result.1.len(),
        forall|i: int| 0 <= i < result.0.len() ==> -100 <= #[trigger] result.0[i] <= 100,
        forall|i: int| 0 <= i < result.1.len() ==> -100 <= #[trigger] result.1[i] <= 100,
{
    let mut a: Vec<i32> = Vec::new();
    let mut b: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            a.len() == i,
            b.len() == i,
            a_vals.len() == n,
            b_vals.len() == n,
            forall|k: int| 0 <= k < i ==> #[trigger] a[k] == a_vals[k],
            forall|k: int| 0 <= k < i ==> #[trigger] b[k] == b_vals[k],
            forall|k: int| 0 <= k < n ==> -100 <= #[trigger] a_vals[k] <= 100,
            forall|k: int| 0 <= k < n ==> -100 <= #[trigger] b_vals[k] <= 100,
        decreases n - i,
    {
        a.push(a_vals[i]);
        b.push(b_vals[i]);
        i = i + 1;
    }
    (a, b)
}

}

use std::io::Write;
use std::collections::HashSet;

struct Rng { state: u64 }
impl Rng {
    fn new(seed: u64) -> Self { Self { state: seed.wrapping_add(0x9E3779B97F4A7C15) } }
    fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.state
    }
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = self.next_u64() % span;
        lo + v as i32
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
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

fn build_input(cases: &[(Vec<i32>, Vec<i32>)]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (a, b) in cases {
        s.push_str(&format!("{}\n", a.len()));
        let p1: Vec<String> = a.iter().map(|v| v.to_string()).collect();
        s.push_str(&p1.join(" "));
        s.push('\n');
        let p2: Vec<String> = b.iter().map(|v| v.to_string()).collect();
        s.push_str(&p2.join(" "));
        s.push('\n');
    }
    s
}

fn build_output(answers: &[bool]) -> String {
    let mut s = String::new();
    for &a in answers {
        s.push_str(if a { "YES\n" } else { "NO\n" });
    }
    s
}

fn build_valid(rng: &mut Rng, n: usize) -> (Vec<i32>, Vec<i32>) {
    let a: Vec<i32> = (0..n).map(|_| rng.gen_range_i32(-100, 99)).collect();
    let mut b = a.clone();
    let k = rng.gen_range_usize(0, n);
    let mut indices: Vec<usize> = (0..n).collect();
    for i in (1..n).rev() {
        let j = (rng.next_u64() as usize) % (i + 1);
        indices.swap(i, j);
    }
    for idx in 0..k {
        let i = indices[idx];
        if b[i] < 100 { b[i] += 1; }
    }
    for i in (1..n).rev() {
        let j = (rng.next_u64() as usize) % (i + 1);
        b.swap(i, j);
    }
    (a, b)
}

fn build_test(rng: &mut Rng, mode: usize) -> (Vec<i32>, Vec<i32>) {
    match mode {
        0 => { let v = rng.gen_range_i32(-100, 100); (vec![v], vec![v]) }
        1 => { let v = rng.gen_range_i32(-100, 99); (vec![v], vec![v + 1]) }
        2 => { let n = rng.gen_range_usize(1, 100); build_valid(rng, n) }
        3 => { let n = 100; build_valid(rng, n) }
        4 => {
            let n = rng.gen_range_usize(1, 100);
            let v = rng.gen_range_i32(-100, 100);
            (vec![v; n], vec![v; n])
        }
        5 => {
            let n = rng.gen_range_usize(1, 100);
            let a: Vec<i32> = vec![0; n];
            let mut b: Vec<i32> = vec![0; n];
            for i in 0..n { b[i] = 1; }
            (a, b)
        }
        6 => {
            let n = rng.gen_range_usize(1, 100);
            (vec![100; n], vec![100; n])
        }
        7 => {
            let n = rng.gen_range_usize(1, 100);
            let a: Vec<i32> = (0..n).map(|_| rng.gen_range_i32(-100, 100)).collect();
            let b: Vec<i32> = (0..n).map(|_| rng.gen_range_i32(-100, 100)).collect();
            (a, b)
        }
        8 => {
            let n = rng.gen_range_usize(1, 100);
            let a: Vec<i32> = (0..n).map(|_| rng.gen_range_i32(-100, 100)).collect();
            let mut b = a.clone();
            for i in (1..n).rev() {
                let j = (rng.next_u64() as usize) % (i + 1);
                b.swap(i, j);
            }
            (a, b)
        }
        9 => { let n = rng.gen_range_usize(1, 100); build_valid(rng, n) }
        _ => {
            let n = rng.gen_range_usize(1, 50);
            let a: Vec<i32> = (0..n).map(|_| rng.gen_range_i32(-100, 100)).collect();
            let b: Vec<i32> = (0..n).map(|_| rng.gen_range_i32(-100, 100)).collect();
            (a, b)
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
    let mut idx = 0usize;
    while count < total {
        let t: usize = if count < 10 { 1 } else { rng.gen_range_usize(1, 20) };
        let mut cases: Vec<(Vec<i32>, Vec<i32>)> = Vec::new();
        for _ in 0..t {
            let mode = idx % modes;
            idx += 1;
            cases.push(build_test(&mut rng, mode));
        }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<bool> = cases.iter().map(|(a, b)| Solution::can_transform(a.clone(), b.clone())).collect();
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

