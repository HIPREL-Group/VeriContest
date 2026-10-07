use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: usize, shift: usize) -> (p: Vec<i32>)
    requires
        2 <= n <= 100_000,
        1 <= shift < n,
    ensures
        2 <= p.len() <= 100_000,
        p.len() == n,
        forall|j: int| 0 <= j < p.len() ==> 1 <= #[trigger] p[j] <= p.len() as int,
{
    let mut p: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            2 <= n <= 100_000,
            1 <= shift < n,
            0 <= i <= n,
            p.len() == i,
            forall|j: int| 0 <= j < p.len() ==> 1 <= #[trigger] p[j] <= n as int,
        decreases n - i,
    {
        // value = ((i + shift) mod n) + 1, in range [1, n]
        let v: usize = ((i + shift) % n) + 1;
        assert(1 <= v <= n);
        p.push(v as i32);
        i = i + 1;
    }
    p
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

fn build_input(cases: &[Vec<i32>]) -> String {
    let mut s = format!("{}\n", cases.len());
    for p in cases {
        s.push_str(&format!("{}\n", p.len()));
        let parts: Vec<String> = p.iter().map(|x| x.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn build_output(answers: &[i32]) -> String {
    let mut s = String::new();
    for a in answers { s.push_str(&format!("{}\n", a)); }
    s
}

fn random_perm(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v: Vec<i32> = (1..=n as i32).collect();
    for i in (1..n).rev() {
        let j = (rng.next_u64() as usize) % (i + 1);
        v.swap(i, j);
    }
    v
}

fn identity(n: usize) -> Vec<i32> {
    (1..=n as i32).collect()
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(31415);
    let mut seen: HashSet<String> = HashSet::new();

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    // Big single cases
    let big_singles: Vec<Vec<i32>> = vec![
        identity(100_000),
        // Full reverse n=10000
        (1..=10000).rev().collect(),
        // Cycle of 2: swap pairs
        (0..100_000).map(|i| if i % 2 == 0 {(i + 2) as i32} else {i as i32}).collect(),
    ];
    for ec in &big_singles {
        if count >= target { break; }
        let cases = vec![ec.clone()];
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<i32> = cases.iter().map(|p| Solution::min_swaps(p.clone())).collect();
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }

    // Bulk multi-test
    while count < target {
        let mode = rng.next_u64() % 4;
        let mut cases: Vec<Vec<i32>> = Vec::new();
        let mut total_n = 0usize;
        match mode {
            0 => {
                let t = rng.gen_range_usize(50, 200);
                for _ in 0..t {
                    let n = rng.gen_range_usize(2, 20);
                    if total_n + n > 100_000 { break; }
                    total_n += n;
                    cases.push(random_perm(&mut rng, n));
                }
            }
            1 => {
                let t = rng.gen_range_usize(2, 5);
                for _ in 0..t {
                    let n = rng.gen_range_usize(5000, 30_000);
                    if total_n + n > 100_000 { break; }
                    total_n += n;
                    cases.push(random_perm(&mut rng, n));
                }
            }
            2 => {
                let t = rng.gen_range_usize(5, 30);
                for _ in 0..t {
                    let n = rng.gen_range_usize(2, 1000);
                    if total_n + n > 100_000 { break; }
                    total_n += n;
                    let pat = rng.next_u64() % 3;
                    let p = match pat {
                        0 => identity(n),
                        1 => (1..=n as i32).rev().collect(),
                        _ => random_perm(&mut rng, n),
                    };
                    cases.push(p);
                }
            }
            _ => {
                let t = rng.gen_range_usize(10, 50);
                for _ in 0..t {
                    let n = rng.gen_range_usize(2, 500);
                    if total_n + n > 100_000 { break; }
                    total_n += n;
                    cases.push(random_perm(&mut rng, n));
                }
            }
        }
        if cases.is_empty() { continue; }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<i32> = cases.iter().map(|p| Solution::min_swaps(p.clone())).collect();
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}

