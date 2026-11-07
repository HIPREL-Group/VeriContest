use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (result: Vec<i32>)
    requires
        1 <= values.len() <= 100000,
        forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 10000,
    ensures
        1 <= result.len() <= 100000,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 10000,
{
    let mut out: Vec<i32> = Vec::new();
    let n = values.len();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            0 <= i <= n,
            out.len() == i,
            forall|k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 10000,
            forall|k: int| 0 <= k < out.len() ==> 1 <= #[trigger] out[k] <= 10000,
        decreases n - i,
    {
        out.push(values[i]);
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
    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let r = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % r) as i128) as i64
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        lo + (self.next_u64() as usize) % (hi - lo + 1)
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

fn build_input(heights: &[i32]) -> String {
    let mut s = format!("{}\n", heights.len());
    for h in heights {
        s.push_str(&format!("{}\n", h));
    }
    s
}

fn build_output(ans: i64) -> String {
    format!("{}\n", ans)
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(0x265BB);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut tries = 0;
    while count < target && tries < target * 100 {
        tries += 1;
        let n = match tries % 7 {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(2, 10),
            2 => rng.gen_range_usize(10, 50),
            3 => rng.gen_range_usize(50, 200),
            4 => rng.gen_range_usize(200, 1000),
            5 => rng.gen_range_usize(1000, 10000),
            _ => rng.gen_range_usize(10000, 100000),
        };
        let max_h = match tries % 4 {
            0 => 10i64,
            1 => 100i64,
            2 => 1000i64,
            _ => 10000i64,
        };
        let heights: Vec<i32> = match tries % 5 {
            0 => (0..n).map(|_| rng.gen_range_i64(1, max_h) as i32).collect(),
            1 => vec![1; n],
            2 => vec![10000; n],
            3 => (1..=(n as i32).min(10000)).collect(),
            _ => (0..n).map(|i| ((i as i64 % 10000) + 1).min(10000) as i32).collect(),
        };
        let heights = heights.into_iter().map(|h| h.max(1).min(10000)).collect::<Vec<i32>>();
        let inp = build_input(&heights);
        if !seen.insert(inp.clone()) { continue; }
        let ans = Solution::min_time(heights);
        let outp = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

