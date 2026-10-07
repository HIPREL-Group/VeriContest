use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: usize, d: i64, heights: Vec<i64>) -> (res: (usize, i64, Vec<i64>))
    requires
        1 <= n <= 1000,
        heights.len() == n,
        1 <= d <= 1000000000,
        forall|i: int| 0 <= i < heights.len() ==> 0 <= #[trigger] heights[i] as int <= 1000000000,
    ensures
        1 <= res.0 <= 1000,
        res.2.len() == res.0,
        1 <= res.1 <= 1000000000,
        forall|i: int| 0 <= i < res.2.len() ==> 0 <= #[trigger] res.2[i] as int <= 1000000000,
{
    (n, d, heights)
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
    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let r = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % r) as i128) as i64
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

fn build_input(n: usize, d: i64, heights: &[i64], sep1: &str, sep2: &str, sep3: &str) -> String {
    let parts: Vec<String> = heights.iter().map(|x| x.to_string()).collect();
    format!("{} {}{}{}{}", n, d, sep1, parts.join(sep2), sep3)
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(321);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |inp: String, n: usize, d: i64, heights: &Vec<i64>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if !seen.insert(inp.clone()) { return; }
        let result = Solution::count_recon_pairs(n, d, heights.clone());
        let outp = format!("{}\n", result);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    while count < target {
        let n = rng.gen_range_usize(1, 50);
        let d = rng.gen_range_i64(1, 1000);
        let heights: Vec<i64> = (0..n).map(|_| rng.gen_range_i64(0, 1000)).collect();
        let mode = (rng.next_u64() % 6) as usize;
        let inp = match mode {
            0 => build_input(n, d, &heights, "\n", " ", "\n"),
            1 => build_input(n, d, &heights, "\n", " ", ""),
            2 => build_input(n, d, &heights, " ", " ", "\n"),
            3 => build_input(n, d, &heights, "\n", "\t", "\n"),
            4 => build_input(n, d, &heights, "\r\n", " ", "\r\n"),
            _ => build_input(n, d, &heights, "\n", "\n", "\n"),
        };
        emit(inp, n, d, &heights, &mut seen, &mut out, &mut count);
    }
}
