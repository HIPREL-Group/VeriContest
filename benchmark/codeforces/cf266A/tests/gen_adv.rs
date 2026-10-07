use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    choices: &Vec<u8>,
) -> (result: (Vec<u8>, usize))
    requires
        1 <= n <= 50,
        choices.len() == n,
        forall|i: int| 0 <= i < choices.len() ==> 0 <= #[trigger] choices[i] as int <= 2,
    ensures
        1 <= result.1 <= 50,
        result.0.len() == result.1,
        forall|i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] as int <= 2,
{
    let mut colors: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            colors.len() == i,
            choices.len() == n,
            forall|k: int| 0 <= k < choices.len() ==> 0 <= #[trigger] choices[k] as int <= 2,
            forall|k: int| 0 <= k < colors.len() ==> 0 <= #[trigger] colors[k] as int <= 2,
        decreases n - i,
    {
        colors.push(choices[i]);
        i = i + 1;
    }
    (colors, n)
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

fn build_input(s: &str) -> String {
    format!("{}\n{}\n", s.len(), s)
}

fn build_output(ans: usize) -> String {
    format!("{}\n", ans)
}

fn solve_str(s: &str) -> usize {
    let colors: Vec<u8> = s.bytes().map(|b| match b {
        b'R' => 0u8, b'G' => 1u8, b'B' => 2u8, _ => 0u8,
    }).collect();
    Solution::min_stones_to_remove(colors, s.len())
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(0x266AA);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let chars = ['R', 'G', 'B'];
    let mut tries = 0;
    while count < target && tries < target * 200 {
        tries += 1;
        let n = match tries % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(2, 10),
            2 => rng.gen_range_usize(10, 25),
            3 => rng.gen_range_usize(25, 40),
            _ => rng.gen_range_usize(40, 50),
        };
        let s: String = match tries % 4 {
            0 => (0..n).map(|_| chars[(rng.next_u64() as usize) % 3]).collect(),
            1 => "R".repeat(n),
            2 => (0..n).map(|i| chars[i % 3]).collect(),
            _ => (0..n).map(|i| chars[i % 2]).collect(),
        };
        let inp = build_input(&s);
        if !seen.insert(inp.clone()) { continue; }
        let ans = solve_str(&s);
        let outp = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

