use vstd::prelude::*;

verus! {

pub fn generate_test_case(raw: Vec<i32>, k: i32) -> (result: (usize, i32, Vec<i32>))
    ensures
        2 <= result.0 <= 100000,
        2 <= result.1 <= 5,
        result.2.len() == result.0,
        forall|j: int| 0 <= j < result.2.len() ==> 1 <= #[trigger] result.2[j] <= 10,
{
    let n = if raw.len() < 2 { 2usize } else if raw.len() > 100000 { 100000usize } else { raw.len() };
    let k = if k < 2 { 2 } else if k > 5 { 5 } else { k };
    let mut a: Vec<i32> = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant
            2 <= n <= 100000, 0 <= i <= n, a.len() == i,
            forall|j: int| 0 <= j < a.len() ==> 1 <= #[trigger] a[j] <= 10,
        decreases n - i,
    {
        let value = if i < raw.len() { raw[i] } else { 1 };
        a.push(if value < 1 { 1 } else if value > 10 { 10 } else { value });
        i += 1;
    }
    (n, k, a)
}


pub fn generate_candidate(
    n: usize,
    k: i32,
    a: Vec<i32>,
) -> (res: (usize, i32, Vec<i32>))
    requires
        2 <= n && n <= 100000,
        2 <= k && k <= 5,
        a.len() == n,
        forall|j: int| 0 <= j && j < n ==> 1 <= a@[j] && a@[j] <= 10,
    ensures
        2 <= res.0 && res.0 <= 100000,
        2 <= res.1 && res.1 <= 5,
        res.2.len() == res.0,
        forall|j: int| 0 <= j && j < res.0 as int ==> 1 <= res.2@[j] && res.2@[j] <= 10,
{
    (n, k, a)
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

type Case = (usize, i32, Vec<i32>);

fn build_input(cases: &[Case]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (n, k, a) in cases {
        s.push_str(&format!("{} {}\n", n, k));
        let p: Vec<String> = a.iter().map(|x| x.to_string()).collect();
        s.push_str(&p.join(" "));
        s.push('\n');
    }
    s
}

fn build_output(answers: &[i32]) -> String {
    let mut s = String::new();
    for a in answers { s.push_str(&format!("{}\n", a)); }
    s
}

fn solve(c: &Case) -> i32 {
    Solution::min_ops(c.0, c.1, c.2.clone())
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(31415);
    let mut seen: HashSet<String> = HashSet::new();

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    // Big single
    let big_singles: Vec<Case> = vec![
        (100_000, 2, vec![1; 100_000]),    // all odd: 1
        (100_000, 5, vec![1; 100_000]),    // need 4 ops
        (100_000, 4, vec![1; 100_000]),    // tricky: all 1, 1 mod 4
        (100_000, 3, vec![10; 100_000]),
    ];
    for ec in &big_singles {
        if count >= target { break; }
        let cases = vec![ec.clone()];
        let cases: Vec<_> = cases.iter().map(|c| generate_test_case(c.2.clone(), c.1)).collect();
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<i32> = cases.iter().map(|c| solve(c)).collect();
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
                    let n = rng.gen_range_usize(2, 20);
                    if total_n + n > 200_000 { break; }
                    total_n += n;
                    let k = rng.gen_range_i64(2, 5) as i32;
                    let a: Vec<i32> = (0..n).map(|_| rng.gen_range_i64(1, 10) as i32).collect();
                    cases.push((n, k, a));
                }
            }
            1 => {
                let t = rng.gen_range_usize(2, 5);
                for _ in 0..t {
                    let n = rng.gen_range_usize(5000, 30_000);
                    if total_n + n > 200_000 { break; }
                    total_n += n;
                    let k = rng.gen_range_i64(2, 5) as i32;
                    let a: Vec<i32> = (0..n).map(|_| rng.gen_range_i64(1, 10) as i32).collect();
                    cases.push((n, k, a));
                }
            }
            2 => {
                let n = rng.gen_range_usize(50_000, 100_000);
                let k = rng.gen_range_i64(2, 5) as i32;
                let a: Vec<i32> = (0..n).map(|_| rng.gen_range_i64(1, 10) as i32).collect();
                cases.push((n, k, a));
            }
            _ => {
                let t = rng.gen_range_usize(5, 30);
                for _ in 0..t {
                    let n = rng.gen_range_usize(2, 500);
                    if total_n + n > 200_000 { break; }
                    total_n += n;
                    let k = rng.gen_range_i64(2, 5) as i32;
                    let a: Vec<i32> = (0..n).map(|_| rng.gen_range_i64(1, 10) as i32).collect();
                    cases.push((n, k, a));
                }
            }
        }
        if cases.is_empty() { continue; }
        let cases: Vec<_> = cases.iter().map(|c| generate_test_case(c.2.clone(), c.1)).collect();
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<i32> = cases.iter().map(|c| solve(c)).collect();
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}
