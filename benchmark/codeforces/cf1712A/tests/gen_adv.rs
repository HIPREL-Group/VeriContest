use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    k: usize,
    perm: Vec<i32>,
) -> (result: (Vec<i32>, usize, usize))
    requires
        perm.len() == n,
        1 <= k <= n <= 100,
        forall|i: int| 0 <= i < n ==> 1 <= #[trigger] perm[i] && perm[i] <= n as int,
    ensures
        result.0.len() == result.1,
        1 <= result.2 <= result.1 <= 100,
        forall|i: int| 0 <= i < result.1 ==> 1 <= #[trigger] result.0[i] && result.0[i] <= result.1 as int,
{
    (perm, n, k)
}

}

use std::io::Write;
use std::collections::HashSet;

struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self { Self(seed.wrapping_add(1)) }
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

type TC = (usize, usize, Vec<i32>);

fn build_input(cases: &[TC]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (n, k, p) in cases {
        s.push_str(&format!("{} {}\n", n, k));
        let parts: Vec<String> = p.iter().map(|x| x.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn build_output(cases: &[TC]) -> String {
    let mut s = String::new();
    for (n, k, p) in cases {
        let ans = Solution::min_swaps_minimize_prefix_sum(p.clone(), *n, *k);
        s.push_str(&format!("{}\n", ans));
    }
    s
}

fn random_perm(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v: Vec<i32> = (1..=n as i32).collect();
    for i in (1..n).rev() {
        let j = rng.gen_range_usize(0, i);
        v.swap(i, j);
    }
    v
}

fn gen_case(rng: &mut Rng, mode: usize) -> TC {
    match mode {
        0 => {
            // small fixed
            let n = rng.gen_range_usize(1, 5);
            let k = rng.gen_range_usize(1, n);
            (n, k, random_perm(rng, n))
        }
        1 => {
            // identity
            let n = rng.gen_range_usize(2, 100);
            let k = rng.gen_range_usize(1, n);
            (n, k, (1..=n as i32).collect())
        }
        2 => {
            // reversed
            let n = rng.gen_range_usize(2, 100);
            let k = rng.gen_range_usize(1, n);
            (n, k, (1..=n as i32).rev().collect())
        }
        3 => {
            // n=k
            let n = rng.gen_range_usize(1, 100);
            (n, n, random_perm(rng, n))
        }
        4 => {
            // k=1
            let n = rng.gen_range_usize(1, 100);
            (n, 1, random_perm(rng, n))
        }
        5 => {
            // largest n
            let n = 100;
            let k = rng.gen_range_usize(1, n);
            (n, k, random_perm(rng, n))
        }
        _ => {
            let n = rng.gen_range_usize(1, 100);
            let k = rng.gen_range_usize(1, n);
            (n, k, random_perm(rng, n))
        }
    }
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(1712);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;
    let mut tries = 0usize;

    while count < target && tries < 100000 {
        tries += 1;
        let t: usize = if count % 4 == 0 { rng.gen_range_usize(2, 20) } else { 1 };
        let mut cases: Vec<TC> = Vec::new();
        for _ in 0..t {
            let mode = (rng.next_u64() as usize) % 7;
            cases.push(gen_case(&mut rng, mode));
        }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let outs = build_output(&cases);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}

