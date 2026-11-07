use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: usize, a: Vec<u32>) -> (result: (usize, Vec<u32>))
    requires
        1 <= n <= 40,
        a.len() == n,
        forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i] <= 1000u32,
    ensures
        1 <= result.0 <= 40,
        result.1.len() == result.0,
        forall|i: int| 0 <= i < result.1.len() ==> #[trigger] result.1[i] <= 1000u32,
{
    (n, a)
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

fn build_one_case(a: &[u32]) -> (String, String) {
    let n = a.len();
    let mut inp = format!("1\n{}\n", n);
    for (i, x) in a.iter().enumerate() {
        if i > 0 { inp.push(' '); }
        inp.push_str(&x.to_string());
    }
    inp.push('\n');
    let ans = Solution::min_swaps(n, a.to_vec());
    let outp = format!("{}\n", ans);
    (inp, outp)
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(1367 * 31);
    let mut seen: HashSet<String> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut tries = 0;
    while count < target && tries < target * 200 {
        tries += 1;
        let n = rng.gen_range_usize(1, 40);
        let mut a: Vec<u32> = Vec::with_capacity(n);
        for _ in 0..n {
            let r = rng.next_u64() % 5;
            let v = match r {
                0 => 0u32,
                1 => 1u32,
                2 => (rng.next_u64() % 1001) as u32,
                3 => (rng.next_u64() % 1001) as u32,
                _ => 1000u32,
            };
            a.push(v);
        }
        let (inp, outp) = build_one_case(&a);
        if !seen.insert(inp.clone()) { continue; }
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}
