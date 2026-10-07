use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_n: usize, fillers: &Vec<i64>) -> (result: (usize, Vec<i64>))
    requires
        2 <= seed_n <= 200000,
        seed_n == fillers.len(),
        forall|i: int| 0 <= i < seed_n ==> 1 <= #[trigger] fillers[i] <= 1000000000,
    ensures
        2 <= result.0 <= 200000,
        result.0 == result.1.len(),
        forall|i: int| 0 <= i < result.0 ==> 1 <= #[trigger] result.1[i] <= 1000000000,
{
    let n = seed_n;
    let mut b: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == fillers.len(),
            2 <= n <= 200000,
            0 <= i <= n,
            b.len() == i,
            forall|j: int| 0 <= j < fillers.len() ==> 1 <= #[trigger] fillers[j] <= 1000000000,
            forall|j: int| 0 <= j < i as int ==> #[trigger] b[j] == fillers[j],
        decreases n - i,
    {
        b.push(fillers[i]);
        i = i + 1;
    }
    (n, b)
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

fn build_input_multi(cases: &[Vec<i64>]) -> String {
    let mut s = format!("{}\n", cases.len());
    for b in cases {
        s.push_str(&format!("{}\n", b.len()));
        let parts: Vec<String> = b.iter().map(|x| x.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn build_output_multi(answers: &[bool]) -> String {
    let mut s = String::new();
    for &a in answers {
        s.push_str(if a { "YES\n" } else { "NO\n" });
    }
    s
}

fn solve(b: &[i64]) -> bool {
    Solution::leftmost_below(b.len(), b.to_vec())
}

fn random_seed(rng: &mut Rng, mode: usize) -> Vec<i64> {
    let n = match mode {
        0 => rng.gen_range_usize(2, 5),
        1 => rng.gen_range_usize(6, 50),
        2 => rng.gen_range_usize(51, 200),
        3 => rng.gen_range_usize(201, 1000),
        4 => rng.gen_range_usize(1001, 5000),
        _ => rng.gen_range_usize(2, 100),
    };
    match mode % 5 {
        0 => (0..n).map(|_| rng.gen_range_i64(1, 1_000_000_000)).collect(),
        1 => {
            let mut v = Vec::with_capacity(n);
            let mut cur: i64 = rng.gen_range_i64(n as i64 + 100, 1_000_000_000);
            for _ in 0..n { v.push(cur); cur -= rng.gen_range_i64(1, 1000); if cur < 1 { cur = 1; } }
            v
        }
        2 => {
            let mut v = Vec::with_capacity(n);
            let mut cur: i64 = 1;
            for _ in 0..n { v.push(cur); cur += rng.gen_range_i64(0, 100); if cur > 1_000_000_000 { cur = 1_000_000_000; } }
            v
        }
        3 => vec![1; n],
        _ => (0..n).map(|_| rng.gen_range_i64(1, 100)).collect(),
    }
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(0x2128CC);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    while count < target {
        let t: usize = if count < 50 { rng.gen_range_usize(1, 5) }
                       else if count < 150 { rng.gen_range_usize(2, 20) }
                       else { rng.gen_range_usize(15, 50) };
        let mut cases: Vec<Vec<i64>> = Vec::with_capacity(t);
        let mut total_n = 0usize;
        for _ in 0..t {
            let mode = rng.gen_range_usize(0, 5);
            let seed_v = random_seed(&mut rng, mode);
            // Validate preconditions
            if seed_v.len() < 2 || seed_v.len() > 200_000 { continue; }
            let mut ok = true;
            for &x in &seed_v {
                if x < 1 || x > 1_000_000_000 { ok = false; break; }
            }
            if !ok { continue; }
            if total_n + seed_v.len() > 200_000 { break; }
            total_n += seed_v.len();
            let (_, v) = generate_test_case(seed_v.len(), &seed_v);
            cases.push(v);
        }
        if cases.is_empty() { continue; }
        let answers: Vec<bool> = cases.iter().map(|c| solve(c)).collect();
        let inp = build_input_multi(&cases);
        let outp = build_output_multi(&answers);
        if !seen.insert(inp.clone()) { continue; }
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}
