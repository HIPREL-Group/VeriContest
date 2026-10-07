use vstd::prelude::*;

verus! {

pub fn generate_test_case(c1: i32, c2: i32, c3: i32, c4: i32) -> (res: (i32, i32, i32, i32))
    requires
        c1 >= 0,
        c2 >= 0,
        c3 >= 0,
        c4 >= 0,
        (c1 as int + c2 as int + c3 as int + c4 as int) <= 100_000,
    ensures
        res.0 >= 0,
        res.1 >= 0,
        res.2 >= 0,
        res.3 >= 0,
        (res.0 as int + res.1 as int + res.2 as int + res.3 as int) <= 100_000,
        res.0 == c1,
        res.1 == c2,
        res.2 == c3,
        res.3 == c4,
{
    (c1, c2, c3, c4)
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
        let x = self.next_u64();
        let v = ((x >> 32) ^ x) as usize;
        lo + v % span
    }
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let x = self.next_u64();
        let v = ((x >> 32) ^ x) % span;
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

fn build_input(groups: &[i32]) -> String {
    let mut s = format!("{}\n", groups.len());
    let parts: Vec<String> = groups.iter().map(|v| v.to_string()).collect();
    s.push_str(&parts.join(" "));
    s.push('\n');
    s
}

fn build_output(ans: i32) -> String { format!("{}\n", ans) }

fn compute(groups: &[i32]) -> i32 {
    let mut c1 = 0i32; let mut c2 = 0i32; let mut c3 = 0i32; let mut c4 = 0i32;
    for &g in groups {
        if g == 1 { c1 += 1; }
        else if g == 2 { c2 += 1; }
        else if g == 3 { c3 += 1; }
        else { c4 += 1; }
    }
    Solution::min_taxis(c1, c2, c3, c4)
}

fn make_test(rng: &mut Rng, mode: usize) -> Vec<i32> {
    match mode {
        0 => vec![1],
        1 => vec![rng.gen_range_i32(1, 4)],
        2 => { let n = rng.gen_range_usize(1, 100); vec![1; n] }
        3 => { let n = rng.gen_range_usize(1, 100); vec![2; n] }
        4 => { let n = rng.gen_range_usize(1, 100); vec![3; n] }
        5 => { let n = rng.gen_range_usize(1, 100); vec![4; n] }
        6 => {
            let n = 100;
            (0..n).map(|_| rng.gen_range_i32(1, 4)).collect()
        }
        7 => {
            let n = rng.gen_range_usize(2, 50);
            let mut v = Vec::new();
            for i in 0..n {
                v.push(if i % 2 == 0 { 1 } else { 3 });
            }
            v
        }
        8 => {
            let n = rng.gen_range_usize(2, 50);
            let mut v = Vec::new();
            for _ in 0..n { v.push(2); }
            v.push(1);
            v
        }
        9 => {
            let n = rng.gen_range_usize(1, 100);
            (0..n).map(|_| rng.gen_range_i32(1, 4)).collect()
        }
        _ => {
            let n = rng.gen_range_usize(1, 100);
            (0..n).map(|_| rng.gen_range_i32(1, 4)).collect()
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
        let mode = idx % modes;
        idx += 1;
        let groups = make_test(&mut rng, mode);
        let inp = build_input(&groups);
        if !seen.insert(inp.clone()) { continue; }
        let ans = compute(&groups);
        let outp = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

