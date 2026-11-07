use vstd::prelude::*;

verus! {

pub fn generate_test_case(digits: &Vec<i64>) -> (res: Vec<i64>)
    requires
        1 <= digits.len() <= 9,
        forall|k: int| 0 <= k < digits.len() ==> 0 <= #[trigger] digits[k] <= 9,
    ensures
        1 <= res.len() <= 9,
        forall|k: int| 0 <= k < res.len() ==> 0 <= #[trigger] res[k] <= 9,
{
    let mut out: Vec<i64> = Vec::new();
    let n = digits.len();
    let mut i: usize = 0;
    while i < n
        invariant
            n == digits.len(),
            1 <= n <= 9,
            0 <= i <= n,
            out.len() == i,
            forall|k: int| 0 <= k < digits.len() ==> 0 <= #[trigger] digits[k] <= 9,
            forall|k: int| 0 <= k < out.len() ==> 0 <= #[trigger] out[k] <= 9,
        decreases n - i,
    {
        let v = digits[i];
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

fn build_input(cases: &[Vec<i64>]) -> String {
    let mut s = format!("{}\n", cases.len());
    for a in cases {
        s.push_str(&format!("{}\n", a.len()));
        let p: Vec<String> = a.iter().map(|x| x.to_string()).collect();
        s.push_str(&p.join(" "));
        s.push('\n');
    }
    s
}

fn build_output(answers: &[i64]) -> String {
    let mut s = String::new();
    for a in answers { s.push_str(&format!("{}\n", a)); }
    s
}

fn random_digits(rng: &mut Rng, n: usize) -> Vec<i64> {
    (0..n).map(|_| rng.gen_range_i64(0, 9)).collect()
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(31415);
    let mut seen: HashSet<String> = HashSet::new();

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    while count < target {
        let t: usize = if count < 30 { rng.gen_range_usize(20, 50) } else { rng.gen_range_usize(30, 100) };
        let mut cases: Vec<Vec<i64>> = Vec::new();
        for _ in 0..t {
            let n = rng.gen_range_usize(1, 9);
            // Try all-zeros, all-9s, etc patterns
            let pat = rng.next_u64() % 5;
            let arr: Vec<i64> = match pat {
                0 => vec![0; n],
                1 => vec![9; n],
                2 => {
                    let mut v = vec![1i64; n];
                    if n > 0 && rng.next_u64() % 2 == 0 { v[0] = 0; }
                    v
                }
                _ => random_digits(&mut rng, n),
            };
            cases.push(arr);
        }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<i64> = cases.iter().map(|a| Solution::max_product_one_increment(a.clone())).collect();
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}

