use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    k: usize,
    q: i64,
    a: Vec<i64>,
) -> (res: (usize, usize, i64, Vec<i64>))
    requires
        1 <= n <= 200000,
        1 <= k <= n,
        -1_000_000_000 <= q <= 1_000_000_000,
        a.len() == n,
        forall|i: int| 0 <= i < n ==> -1_000_000_000 <= #[trigger] a[i] <= 1_000_000_000,
    ensures
        ({
            let (nn, kk, qq, aa) = res;
            &&& 1 <= nn <= 200000
            &&& 1 <= kk <= nn
            &&& aa.len() == nn
            &&& forall|i: int| 0 <= i < nn as int ==> -1_000_000_000 <= #[trigger] aa[i] <= 1_000_000_000
        }),
{
    (n, k, q, a)
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

type Case = (usize, usize, i64, Vec<i64>);

fn build_input(cases: &[Case]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (n, k, q, a) in cases {
        s.push_str(&format!("{} {} {}\n", n, k, q));
        let parts: Vec<String> = a.iter().map(|x| x.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn build_output(answers: &[i64]) -> String {
    let mut s = String::new();
    for a in answers { s.push_str(&format!("{}\n", a)); }
    s
}

fn solve(c: &Case) -> i64 {
    Solution::count_vacations(c.0, c.1, c.2, c.3.clone())
}

fn random_case(rng: &mut Rng, max_n: usize) -> Case {
    let n = rng.gen_range_usize(1, max_n);
    let k = rng.gen_range_usize(1, n);
    let q = rng.gen_range_i64(-1_000_000_000, 1_000_000_000);
    let a: Vec<i64> = (0..n).map(|_| rng.gen_range_i64(-1_000_000_000, 1_000_000_000)).collect();
    (n, k, q, a)
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(31415);
    let mut seen: HashSet<String> = HashSet::new();

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    // Single big cases
    let big_singles: Vec<Case> = vec![
        (200_000, 1, 1_000_000_000, vec![0; 200_000]),
        (200_000, 200_000, 1_000_000_000, vec![0; 200_000]),
        (200_000, 1, -1_000_000_000, vec![0; 200_000]),  // 0 valid
        (200_000, 100, 0, (0..200_000).map(|i| if i % 2 == 0 {0i64} else {1}).collect()),
    ];
    for ec in &big_singles {
        if count >= target { break; }
        let cases = vec![ec.clone()];
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<i64> = cases.iter().map(|c| solve(c)).collect();
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }

    while count < target {
        let mode = rng.next_u64() % 4;
        let mut cases: Vec<Case> = Vec::new();
        let mut total_n = 0usize;
        match mode {
            0 => {
                let t = rng.gen_range_usize(20, 100);
                for _ in 0..t {
                    let c = random_case(&mut rng, 30);
                    if total_n + c.0 > 200_000 { break; }
                    total_n += c.0;
                    cases.push(c);
                }
            }
            1 => {
                let t = rng.gen_range_usize(2, 5);
                for _ in 0..t {
                    let c = random_case(&mut rng, 5000);
                    if total_n + c.0 > 200_000 { break; }
                    total_n += c.0;
                    cases.push(c);
                }
            }
            2 => {
                let n = rng.gen_range_usize(20_000, 100_000);
                let k = rng.gen_range_usize(1, n);
                let q = rng.gen_range_i64(-1_000_000_000, 1_000_000_000);
                let a: Vec<i64> = (0..n).map(|_| rng.gen_range_i64(-1_000_000_000, 1_000_000_000)).collect();
                cases.push((n, k, q, a));
            }
            _ => {
                let t = rng.gen_range_usize(5, 30);
                for _ in 0..t {
                    let c = random_case(&mut rng, 500);
                    if total_n + c.0 > 200_000 { break; }
                    total_n += c.0;
                    cases.push(c);
                }
            }
        }
        if cases.is_empty() { continue; }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<i64> = cases.iter().map(|c| solve(c)).collect();
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}

