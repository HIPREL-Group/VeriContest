use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    seed_choices: Vec<usize>,
) -> (result: (usize, Vec<i64>))
    requires
        1 <= n <= 100000,
        seed_choices.len() == n,
        forall|i: int| 0 <= i < seed_choices.len() ==> #[trigger] seed_choices[i] < n,
    ensures
        1 <= result.0 <= 100000,
        result.1.len() == result.0,
        forall|i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i] <= result.0 as i64,
{
    let mut v: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            1 <= n <= 100000,
            v.len() == i,
            seed_choices.len() == n,
            forall|k: int| 0 <= k < seed_choices.len() ==> #[trigger] seed_choices[k] < n,
            forall|k: int| 0 <= k < i ==> 1i64 <= #[trigger] v[k] <= n as i64,
        decreases n - i,
    {
        let s = seed_choices[i];
        let r: usize = s % n;
        assert(r < n);
        let val: i64 = r as i64 + 1i64;
        assert(1i64 <= val <= n as i64);
        v.push(val);
        i = i + 1;
    }
    (n, v)
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

fn build_input(perm: &Vec<i64>) -> String {
    let mut s = format!("1\n{}\n", perm.len());
    for (i, x) in perm.iter().enumerate() {
        if i > 0 { s.push(' '); }
        s.push_str(&x.to_string());
    }
    s.push('\n');
    s
}

fn build_output(ans: usize) -> String { format!("{}\n", ans) }

fn random_permutation(n: usize, rng: &mut Rng) -> Vec<i64> {
    let mut v: Vec<i64> = (1..=(n as i64)).collect();
    for i in 0..n {
        let j = rng.gen_range_usize(i, n - 1);
        v.swap(i, j);
    }
    v
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(0x1686AA);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut tries = 0;
    while count < target && tries < target * 50 {
        tries += 1;
        let n = match tries % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(2, 10),
            2 => rng.gen_range_usize(10, 50),
            3 => rng.gen_range_usize(50, 500),
            _ => rng.gen_range_usize(500, 5000),
        };
        let perm = random_permutation(n, &mut rng);
        let inp = build_input(&perm);
        if !seen.insert(inp.clone()) { continue; }
        let ans = Solution::max_odd_subarrays(n, perm.clone());
        let outp = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}
