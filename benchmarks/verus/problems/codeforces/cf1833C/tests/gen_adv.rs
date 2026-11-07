use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    fillers: &Vec<u32>,
) -> (result: (Vec<u32>, usize))
    requires
        1 <= n <= 200_000,
        fillers.len() == n,
        forall|i: int| 0 <= i < fillers.len() ==> 1 <= #[trigger] fillers[i] <= 1_000_000_000,
    ensures
        1 <= result.1 <= 200_000,
        result.0.len() == result.1,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 1_000_000_000,
{
    let mut a: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == fillers.len(),
            1 <= n <= 200_000,
            0 <= i <= n,
            a.len() == i,
            forall|j: int| 0 <= j < fillers.len() ==> 1 <= #[trigger] fillers[j] <= 1_000_000_000,
            forall|j: int| 0 <= j < a.len() ==> 1 <= #[trigger] a[j] <= 1_000_000_000,
        decreases n - i,
    {
        a.push(fillers[i]);
        i = i + 1;
    }
    (a, n)
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
    fn gen_range_u32(&mut self, lo: u32, hi: u32) -> u32 {
        let r = (hi as u64 - lo as u64 + 1);
        lo + (self.next_u64() % r) as u32
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

fn build_input(cases: &[Vec<u32>]) -> String {
    let mut s = format!("{}\n", cases.len());
    for a in cases {
        s.push_str(&format!("{}\n", a.len()));
        let parts: Vec<String> = a.iter().map(|x| x.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn build_output(answers: &[bool]) -> String {
    let mut s = String::new();
    for &b in answers {
        s.push_str(if b { "YES\n" } else { "NO\n" });
    }
    s
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(0x1833C);
    let mut seen: HashSet<String> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;
    let mut tries = 0;
    while count < target && tries < target * 100 {
        tries += 1;
        let t = rng.gen_range_usize(1, 8);
        let mut cases: Vec<Vec<u32>> = Vec::new();
        for _ in 0..t {
            let n = match tries % 5 {
                0 => rng.gen_range_usize(1, 5),
                1 => rng.gen_range_usize(1, 20),
                2 => rng.gen_range_usize(20, 100),
                3 => rng.gen_range_usize(50, 500),
                _ => rng.gen_range_usize(100, 1000),
            };
            let mut fillers: Vec<u32> = Vec::with_capacity(n);
            for _ in 0..n {
                let mode = rng.next_u64() % 6;
                let v = match mode {
                    0 => 2u32 * rng.gen_range_u32(1, 500),  // even
                    1 => 2u32 * rng.gen_range_u32(0, 500) + 1,  // odd
                    2 => rng.gen_range_u32(1, 100),
                    3 => rng.gen_range_u32(1, 1_000_000_000),
                    _ => rng.gen_range_u32(1, 10),
                };
                fillers.push(v);
            }
            let (a, _) = generate_test_case(n, &fillers);
            cases.push(a);
        }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<bool> = cases.iter().map(|a| Solution::vlad_beautiful(a.clone(), a.len())).collect();
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}
