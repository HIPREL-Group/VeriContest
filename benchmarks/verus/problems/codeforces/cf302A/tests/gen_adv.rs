use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    raw_a: Vec<i8>,
    raw_qls: Vec<usize>,
    raw_qrs: Vec<usize>,
) -> (result: (Vec<i8>, Vec<usize>, Vec<usize>))
    requires
        1 <= raw_a.len() <= 200000,
        1 <= raw_qls.len() <= 200000,
        raw_qls.len() == raw_qrs.len(),
        forall|i: int| 0 <= i < raw_a.len() ==> #[trigger] raw_a[i] == 1i8 || raw_a[i] == -1i8,
        forall|i: int| 0 <= i < raw_qls.len() ==> 1 <= #[trigger] raw_qls[i] <= raw_qrs[i] <= raw_a.len(),
    ensures
        1 <= result.0.len() <= 200000,
        1 <= result.1.len() <= 200000,
        result.1.len() == result.2.len(),
        forall|i: int| 0 <= i < result.0.len() ==> #[trigger] result.0[i] == 1i8 || result.0[i] == -1i8,
        forall|i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i] <= result.2[i] <= result.0.len(),
{
    (raw_a, raw_qls, raw_qrs)
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

fn build_input(a: &Vec<i8>, qls: &Vec<usize>, qrs: &Vec<usize>) -> String {
    let n = a.len();
    let m = qls.len();
    let mut s = format!("{} {}\n", n, m);
    for i in 0..n {
        if i > 0 { s.push(' '); }
        s.push_str(&format!("{}", a[i]));
    }
    s.push('\n');
    for i in 0..m {
        s.push_str(&format!("{} {}\n", qls[i], qrs[i]));
    }
    s
}

fn build_output(ans: &Vec<u8>) -> String {
    let mut s = String::new();
    for v in ans {
        s.push_str(&format!("{}\n", v));
    }
    s
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(0x302AA);
    let mut seen: HashSet<String> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut tries = 0usize;
    while count < target && tries < target * 200 {
        tries += 1;
        let n = match tries % 6 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(5, 20),
            2 => rng.gen_range_usize(20, 100),
            3 => rng.gen_range_usize(100, 500),
            4 => rng.gen_range_usize(500, 2000),
            _ => rng.gen_range_usize(2000, 5000),
        };
        let m = rng.gen_range_usize(1, n.min(30));
        let a: Vec<i8> = (0..n).map(|_| if rng.next_u64() % 2 == 0 { 1i8 } else { -1i8 }).collect();
        let mut qls: Vec<usize> = Vec::new();
        let mut qrs: Vec<usize> = Vec::new();
        for _ in 0..m {
            let l = rng.gen_range_usize(1, n);
            let r = rng.gen_range_usize(l, n);
            qls.push(l);
            qrs.push(r);
        }
        let inp = build_input(&a, &qls, &qrs);
        if !seen.insert(inp.clone()) { continue; }
        let ans = Solution::answer_queries(a, qls, qrs);
        let outp = build_output(&ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}
