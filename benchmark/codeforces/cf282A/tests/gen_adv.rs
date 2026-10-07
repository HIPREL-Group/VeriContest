use vstd::prelude::*;

verus! {

pub fn generate_test_case(ops: &Vec<i8>) -> (res: Vec<i32>)
    requires
        1 <= ops.len() <= 150,
        forall|i: int| 0 <= i < ops.len() ==> (#[trigger] ops[i] == 1i8 || ops[i] == -1i8),
    ensures
        1 <= res.len() <= 150,
        res.len() == ops.len(),
        forall|i: int| 0 <= i < res.len() ==> (#[trigger] res[i] == 1i32 || res[i] == -1i32),
{
    let mut out: Vec<i32> = Vec::new();
    let n = ops.len();
    let mut i: usize = 0;
    while i < n
        invariant
            n == ops.len(),
            0 <= i <= n,
            out.len() == i,
            forall|k: int| 0 <= k < ops.len() ==> (#[trigger] ops[k] == 1i8 || ops[k] == -1i8),
            forall|k: int| 0 <= k < i as int ==> (#[trigger] out[k] == 1i32 || out[k] == -1i32),
        decreases n - i,
    {
        let v: i32 = if ops[i] == 1i8 { 1i32 } else { -1i32 };
        out.push(v);
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
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
    fn gen_bool(&mut self) -> bool { self.next_u64() % 2 == 0 }
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

fn build_ops(mode: usize, n: usize, rng: &mut Rng) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => { for _ in 0..n { v.push(1); } }
        1 => { for _ in 0..n { v.push(-1); } }
        2 => { for i in 0..n { v.push(if i % 2 == 0 { 1 } else { -1 }); } }
        3 => { for i in 0..n { v.push(if i % 2 == 0 { -1 } else { 1 }); } }
        4 => {
            let half = n / 2;
            for _ in 0..half { v.push(1); }
            for _ in half..n { v.push(-1); }
        }
        5 => {
            let half = n / 2;
            for _ in 0..half { v.push(-1); }
            for _ in half..n { v.push(1); }
        }
        6 => { for _ in 0..n { v.push(if rng.gen_bool() { 1 } else { -1 }); } }
        7 => { for i in 0..n { v.push(if i == n - 1 { -1 } else { 1 }); } }
        8 => { for i in 0..n { v.push(if i == 0 { -1 } else { 1 }); } }
        _ => { for _ in 0..n { v.push(if rng.gen_bool() { 1 } else { -1 }); } }
    }
    v
}

fn build_input(ops: &[i32], rng: &mut Rng) -> String {
    let mut s = format!("{}\n", ops.len());
    for &op in ops {
        if op == 1 {
            if rng.gen_bool() { s.push_str("++X\n"); } else { s.push_str("X++\n"); }
        } else {
            if rng.gen_bool() { s.push_str("--X\n"); } else { s.push_str("X--\n"); }
        }
    }
    s
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(1);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let modes = 10usize;
    let mut t = 0usize;
    while count < target {
        let mode = t % modes;
        let n = match t % 7 {
            0 => 1,
            1 => 150,
            2 => 2,
            3 => rng.gen_range_usize(1, 150),
            4 => rng.gen_range_usize(1, 20),
            5 => 75,
            _ => rng.gen_range_usize(1, 150),
        };
        let ops = build_ops(mode, n, &mut rng);
        let key = format!("{:?}", ops);
        t += 1;
        if !seen.insert(key) { continue; }
        let inp = build_input(&ops, &mut rng);
        let ans = Solution::final_x_value(ops.clone());
        let outs = format!("{}\n", ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
        if t > 100000 { break; }
    }
}

