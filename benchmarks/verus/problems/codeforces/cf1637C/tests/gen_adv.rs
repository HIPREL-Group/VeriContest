use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    fillers: &Vec<i64>,
) -> (a: Vec<i64>)
    requires
        3 <= n <= 100_000,
        fillers.len() == n,
        forall|i: int| 0 <= i < fillers.len() ==> 1 <= #[trigger] fillers[i] <= 1_000_000_000,
    ensures
        3 <= a.len() <= 100_000,
        a.len() == n,
        forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] && a[i] <= 1_000_000_000,
{
    let mut a: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            3 <= n <= 100_000,
            fillers.len() == n,
            0 <= i <= n,
            a.len() == i,
            forall|k: int| 0 <= k < fillers.len() ==> 1 <= #[trigger] fillers[k] <= 1_000_000_000,
            forall|k: int| 0 <= k < a.len() ==> 1 <= #[trigger] a[k] <= 1_000_000_000,
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

fn build_output(answers: &[Option<i64>]) -> String {
    let mut s = String::new();
    for &a in answers {
        match a {
            None => s.push_str("-1\n"),
            Some(k) => s.push_str(&format!("{}\n", k)),
        }
    }
    s
}

fn make_test(rng: &mut Rng, mode: usize) -> Vec<i64> {
    match mode {
        0 => vec![rng.gen_range_i64(1, 100), 1, rng.gen_range_i64(1, 100)],
        1 => {
            let v = rng.gen_range_i64(1, 100) * 2;
            vec![1, v, 1]
        }
        2 => {
            let n = rng.gen_range_usize(3, 100);
            (0..n).map(|_| rng.gen_range_i64(1, 1_000_000_000)).collect()
        }
        3 => {
            let n = rng.gen_range_usize(3, 100);
            vec![1; n]
        }
        4 => {
            let n = rng.gen_range_usize(4, 50);
            let mut v = vec![1; n];
            v[1] = 2;
            v
        }
        5 => {
            let n = rng.gen_range_usize(3, 30);
            (0..n).map(|i| if i == 0 || i == n-1 { rng.gen_range_i64(1, 100) } else { 1_000_000_000 }).collect()
        }
        6 => {
            let n = 100;
            (0..n).map(|_| rng.gen_range_i64(1, 1_000_000_000)).collect()
        }
        7 => {
            let n = rng.gen_range_usize(4, 50);
            (0..n).map(|i| if i % 2 == 0 { 1 } else { 2 }).collect()
        }
        8 => {
            let n = rng.gen_range_usize(4, 50);
            (0..n).map(|i| if i == 0 || i == n-1 { 1 } else { 2 * rng.gen_range_i64(1, 100) + 1 }).collect()
        }
        9 => {
            // Lots of even mid values
            let n = rng.gen_range_usize(3, 50);
            (0..n).map(|_| 2 * rng.gen_range_i64(1, 100)).collect()
        }
        _ => {
            let n = rng.gen_range_usize(3, 50);
            (0..n).map(|_| rng.gen_range_i64(1, 100)).collect()
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
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<Option<i64>> = cases.iter().map(|a| Solution::minimum_stone_operations(a.clone())).collect();
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

