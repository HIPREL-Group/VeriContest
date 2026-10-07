use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    vals: &Vec<i32>,
) -> (a: Vec<i32>)
    requires
        2 <= vals.len() <= 100000,
        forall|i: int| 0 <= i < vals.len() ==> -10000 <= #[trigger] vals[i] <= 10000,
        forall|i: int| 0 <= i < vals.len() ==> #[trigger] vals[i] != 0,
    ensures
        2 <= a.len() <= 100000,
        forall|i: int| 0 <= i < a.len() ==> -10000 <= #[trigger] a[i] <= 10000,
        forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] != 0,
{
    let n = vals.len();
    let mut a: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == vals.len(),
            2 <= n <= 100000,
            0 <= i <= n,
            a.len() == i,
            forall|k: int| 0 <= k < vals.len() ==> -10000 <= #[trigger] vals[k] <= 10000,
            forall|k: int| 0 <= k < vals.len() ==> #[trigger] vals[k] != 0,
            forall|k: int| 0 <= k < i as int ==> #[trigger] a[k] == vals[k],
        decreases n - i,
    {
        a.push(vals[i]);
        i = i + 1;
    }
    a
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
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
    fn gen_nonzero_i32(&mut self, lo: i32, hi: i32) -> i32 {
        loop {
            let v = self.gen_range_i32(lo, hi);
            if v != 0 { return v; }
        }
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

fn build_test(mode: usize, rng: &mut Rng) -> Vec<i32> {
    match mode {
        0 => { let a = rng.gen_nonzero_i32(-10000, 10000); let b = rng.gen_nonzero_i32(-10000, 10000); vec![a, b] }
        1 => { let n = rng.gen_range_usize(2, 100); vec![1i32; n] }
        2 => { let n = rng.gen_range_usize(2, 100); vec![-1i32; n] }
        3 => {
            let n = rng.gen_range_usize(2, 50);
            let mut v = Vec::new();
            for _ in 0..n {
                if rng.next_u64() % 2 == 0 { v.push(10000); } else { v.push(-10000); }
            }
            v
        }
        4 => {
            let n = 10000;
            let mut v = Vec::with_capacity(n);
            for _ in 0..n { v.push(rng.gen_nonzero_i32(-10000, 10000)); }
            v
        }
        5 => {
            let n = rng.gen_range_usize(2, 20);
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_nonzero_i32(-3, 3)); }
            v
        }
        6 => {
            let n = rng.gen_range_usize(2, 50) * 2;
            let mut v = Vec::new();
            for _ in 0..n/2 {
                let x = rng.gen_nonzero_i32(-10000, 10000);
                v.push(x); v.push(-x);
            }
            v
        }
        7 => {
            let n = rng.gen_range_usize(2, 100);
            let x = rng.gen_nonzero_i32(1, 10000);
            let mut v = Vec::new();
            for i in 0..n {
                if i % 2 == 0 { v.push(x); } else { v.push(-x); }
            }
            v
        }
        8 => {
            let n = rng.gen_range_usize(2, 100);
            let mut v = Vec::new();
            v.push(10000);
            for _ in 1..n { v.push(rng.gen_nonzero_i32(-2, 2)); }
            v
        }
        9 => {
            let n = 2 * rng.gen_range_usize(1, 50) + 1;
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_nonzero_i32(-10000, 10000)); }
            v
        }
        _ => {
            let n = rng.gen_range_usize(2, 1000);
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_nonzero_i32(-10000, 10000)); }
            v
        }
    }
}

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

fn build_output(answers: &[Vec<i32>]) -> String {
    let mut s = String::new();
    for b in answers {
        let parts: Vec<String> = b.iter().map(|v| v.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
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
        let t: usize = if count < 10 { 1 } else { rng.gen_range_usize(1, 10) };
        let mut cases: Vec<Vec<i32>> = Vec::new();
        for _ in 0..t {
            let mode = idx % modes;
            idx += 1;
            cases.push(build_test(mode, &mut rng));
        }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<Vec<i32>> = cases.iter().map(|a| Solution::construct_coeffs(a.clone())).collect();
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

