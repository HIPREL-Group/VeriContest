use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (result: (Vec<i32>, usize))
    requires
        1 <= values.len() <= 1000,
        forall|i: int| 0 <= i < values.len() ==> 0 <= #[trigger] values[i] as int <= 10000,
    ensures
        1 <= result.1 <= 1000,
        result.0.len() == result.1,
        forall|i: int| 0 <= i < result.0.len() as int ==> 0 <= #[trigger] result.0[i] as int <= 10000,
{
    let n = values.len();
    let mut out: Vec<i32> = Vec::new();
    let mut idx: usize = 0;
    while idx < n
        invariant
            n == values.len(),
            1 <= n <= 1000,
            0 <= idx <= n,
            out.len() == idx,
            forall|i: int| 0 <= i < values.len() ==> 0 <= #[trigger] values[i] as int <= 10000,
            forall|k: int| 0 <= k < out.len() as int ==> out[k] == values[k],
            forall|k: int| 0 <= k < out.len() as int ==> 0 <= #[trigger] out[k] as int <= 10000,
        decreases n - idx,
    {
        let v = values[idx];
        out.push(v);
        idx = idx + 1;
    }
    (out, n)
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
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = self.next_u64() % span;
        lo + v as i32
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

fn build_input(n: usize, points: &[i32]) -> String {
    let mut s = format!("{}\n", n);
    let parts: Vec<String> = points.iter().map(|v| v.to_string()).collect();
    s.push_str(&parts.join(" "));
    s.push('\n');
    s
}

fn build_output(ans: usize) -> String { format!("{}\n", ans) }

fn adversarial_mode(rng: &mut Rng, mode: usize) -> Vec<i32> {
    match mode {
        0 => vec![rng.gen_range_i32(0, 10000)],
        1 => {
            let n = rng.gen_range_usize(2, 1000);
            let v = rng.gen_range_i32(0, 10000);
            vec![v; n]
        }
        2 => {
            let n = rng.gen_range_usize(2, 500);
            let mut res = Vec::with_capacity(n);
            for i in 0..n { res.push(((i as i32) * 20).min(10000)); }
            res
        }
        3 => {
            let n = rng.gen_range_usize(2, 500);
            let mut res = Vec::with_capacity(n);
            for i in 0..n { res.push((10000 - (i as i32) * 20).max(0)); }
            res
        }
        4 => {
            let n = 1000;
            let mut res = Vec::with_capacity(n);
            for _ in 0..n { res.push(rng.gen_range_i32(0, 10000)); }
            res
        }
        5 => { let n = rng.gen_range_usize(1, 1000); vec![0i32; n] }
        6 => { let n = rng.gen_range_usize(1, 1000); vec![10000i32; n] }
        7 => {
            let n = rng.gen_range_usize(2, 500);
            let mut res = Vec::with_capacity(n);
            for i in 0..n { res.push(if i % 2 == 0 { 0 } else { 10000 }); }
            res
        }
        8 => {
            let n = rng.gen_range_usize(2, 500);
            let mut res = Vec::with_capacity(n);
            for _ in 0..n { res.push(rng.gen_range_i32(0, 5)); }
            res
        }
        9 => {
            let n = rng.gen_range_usize(2, 200);
            let mut res = Vec::with_capacity(n);
            res.push(10000);
            for _ in 1..n { res.push(rng.gen_range_i32(1, 9999)); }
            res
        }
        _ => {
            let n = rng.gen_range_usize(1, 1000);
            let mut res = Vec::with_capacity(n);
            for _ in 0..n { res.push(rng.gen_range_i32(0, 10000)); }
            res
        }
    }
}

fn main() {
    let mut rng = Rng::new(1);
    let total = 200;
    let modes = 10;

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut seen: HashSet<String> = HashSet::new();
    let mut count = 0;
    let mut t = 0;
    while count < total {
        let mode = t % modes;
        t += 1;
        let pts = adversarial_mode(&mut rng, mode);
        let n = pts.len();
        let inp = build_input(n, &pts);
        if !seen.insert(inp.clone()) { continue; }
        let ans = Solution::count_amazing_performances(pts.clone(), n);
        let outp = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

