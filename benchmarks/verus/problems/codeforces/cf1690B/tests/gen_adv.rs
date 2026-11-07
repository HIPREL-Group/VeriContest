use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    k: i32,
    base_b: &Vec<i32>,
    zero_mask: &Vec<bool>,
) -> (result: (usize, Vec<i32>, Vec<i32>))
    requires
        1 <= n <= 50000,
        base_b.len() == n,
        zero_mask.len() == n,
        0 <= k <= 1000000000,
        forall|i: int| 0 <= i < n ==> 0 <= #[trigger] base_b[i] <= 1000000000 - k as int,
    ensures
        result.0 == n,
        result.1.len() == n,
        result.2.len() == n,
        forall|i: int| 0 <= i < n ==> 0 <= #[trigger] result.1@[i] <= 1000000000,
        forall|i: int| 0 <= i < n ==> 0 <= #[trigger] result.2@[i] <= 1000000000,
{
    let mut a: Vec<i32> = Vec::new();
    let mut b: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            a.len() == i,
            b.len() == i,
            base_b.len() == n,
            zero_mask.len() == n,
            0 <= k <= 1000000000,
            forall|j: int| 0 <= j < n ==> 0 <= #[trigger] base_b[j] <= 1000000000 - k as int,
            forall|j: int| 0 <= j < i as int ==> 0 <= #[trigger] a@[j] <= 1000000000,
            forall|j: int| 0 <= j < i as int ==> 0 <= #[trigger] b@[j] <= 1000000000,
        decreases n - i,
    {
        let bv = base_b[i];
        let av: i32 = bv + k;
        if zero_mask[i] {
            // set b[i] = 0, a[i] stays av (which is >= 0)
            b.push(0);
            a.push(av);
        } else {
            b.push(bv);
            a.push(av);
        }
        i = i + 1;
    }
    (n, a, b)
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
    for &a in answers { s.push_str(if a { "YES\n" } else { "NO\n" }); }
    s
}

fn build_valid(rng: &mut Rng, n: usize, max_a: i32) -> (Vec<i32>, Vec<i32>) {
    let a: Vec<i32> = (0..n).map(|_| rng.gen_range_i64(0, max_a as i64) as i32).collect();
    let k = rng.gen_range_i64(0, max_a as i64 / 2) as i32;
    let b: Vec<i32> = a.iter().map(|&x| if x >= k { x - k } else { 0 }).collect();
    (a, b)
}

fn make_test(rng: &mut Rng, mode: usize) -> (Vec<i32>, Vec<i32>) {
    match mode {
        0 => (vec![rng.gen_range_i64(0, 1_000_000_000) as i32], vec![0]),
        1 => (vec![0], vec![rng.gen_range_i64(0, 1_000_000_000) as i32]),
        2 => { let n = rng.gen_range_usize(1, 50); build_valid(rng, n, 100) }
        3 => {
            let n = rng.gen_range_usize(1, 50);
            (vec![1_000_000_000; n], vec![0; n])
        }
        4 => {
            let n = rng.gen_range_usize(1, 50);
            let v: Vec<i32> = (0..n).map(|_| rng.gen_range_i64(0, 1_000_000_000) as i32).collect();
            (v.clone(), v)
        }
        5 => { let n = rng.gen_range_usize(1, 100); build_valid(rng, n, 1_000_000_000) }
        6 => {
            let n = rng.gen_range_usize(1, 50);
            let a: Vec<i32> = (0..n).map(|_| rng.gen_range_i64(0, 100) as i32).collect();
            let b: Vec<i32> = (0..n).map(|_| rng.gen_range_i64(0, 100) as i32).collect();
            (a, b)
        }
        7 => {
            let n = 100;
            build_valid(rng, n, 1_000_000_000)
        }
        8 => {
            // a == b mostly, but one differs
            let n = rng.gen_range_usize(2, 50);
            let mut a: Vec<i32> = (0..n).map(|_| rng.gen_range_i64(0, 100) as i32).collect();
            let mut b = a.clone();
            let pos = rng.gen_range_usize(0, n - 1);
            b[pos] = b[pos].saturating_add(1);
            (a, b)
        }
        9 => {
            let n = rng.gen_range_usize(1, 30);
            (vec![0; n], vec![0; n])
        }
        _ => {
            let n = rng.gen_range_usize(1, 50);
            let a: Vec<i32> = (0..n).map(|_| rng.gen_range_i64(0, 1_000_000_000) as i32).collect();
            let b: Vec<i32> = (0..n).map(|_| rng.gen_range_i64(0, 1_000_000_000) as i32).collect();
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
    let mut idx = 0;
    while count < total {
        let t: usize = if count < 10 { 1 } else { rng.gen_range_usize(1, 10) };
        let mut cases: Vec<(Vec<i32>, Vec<i32>)> = Vec::new();
        for _ in 0..t {
            let mode = idx % modes;
            idx += 1;
            cases.push(make_test(&mut rng, mode));
        }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<bool> = cases.iter().map(|(a, b)| Solution::is_possible(a.len(), a.clone(), b.clone())).collect();
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

