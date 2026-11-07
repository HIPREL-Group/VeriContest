use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    raw_left: Vec<u8>,
    raw_right: Vec<u8>,
) -> (result: (Vec<u8>, Vec<u8>, usize))
    requires
        2 <= n <= 10000,
        raw_left.len() == n,
        raw_right.len() == n,
        forall|i: int| 0 <= i < raw_left.len() ==> #[trigger] raw_left[i] <= 1u8,
        forall|i: int| 0 <= i < raw_right.len() ==> #[trigger] raw_right[i] <= 1u8,
    ensures
        2 <= result.2 <= 10000,
        result.0.len() == result.2,
        result.1.len() == result.2,
        forall|i: int| 0 <= i < result.0.len() ==> #[trigger] result.0[i] <= 1u8,
        forall|i: int| 0 <= i < result.1.len() ==> #[trigger] result.1[i] <= 1u8,
{
    (raw_left, raw_right, n)
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

fn build_input(left: &Vec<u8>, right: &Vec<u8>) -> String {
    let n = left.len();
    let mut s = format!("{}\n", n);
    for i in 0..n {
        s.push_str(&format!("{} {}\n", left[i], right[i]));
    }
    s
}

fn build_output(ans: usize) -> String {
    format!("{}\n", ans)
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(0x248AA);
    let mut seen: HashSet<String> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut tries = 0usize;
    while count < target && tries < target * 200 {
        tries += 1;
        let n = match tries % 6 {
            0 => rng.gen_range_usize(2, 5),
            1 => rng.gen_range_usize(5, 20),
            2 => rng.gen_range_usize(20, 100),
            3 => rng.gen_range_usize(100, 1000),
            4 => rng.gen_range_usize(1000, 5000),
            _ => rng.gen_range_usize(5000, 10000),
        };
        let left: Vec<u8> = (0..n).map(|_| (rng.next_u64() % 2) as u8).collect();
        let right: Vec<u8> = (0..n).map(|_| (rng.next_u64() % 2) as u8).collect();
        let inp = build_input(&left, &right);
        if !seen.insert(inp.clone()) { continue; }
        let ans = Solution::min_seconds(left.clone(), right.clone(), n);
        let outp = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}
