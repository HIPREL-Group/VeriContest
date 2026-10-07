use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    raw_b: Vec<u32>,
    raw_s: u32,
) -> (result: (Vec<u32>, usize, u32))
    requires
        1 <= raw_b.len() <= 50,
        1 <= raw_s <= 1000,
        forall|i: int| 0 <= i < raw_b.len() ==> 1 <= #[trigger] raw_b[i] <= 50,
        forall|i: int, j: int| 0 <= i < j < raw_b.len() ==> raw_b[i] != raw_b[j],
    ensures
        1 <= result.1 <= 50,
        1 <= result.2 <= 1000,
        result.0.len() == result.1,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 50,
        forall|i: int, j: int| 0 <= i < j < result.0.len() ==> result.0[i] != result.0[j],
{
    let n = raw_b.len();
    (raw_b, n, raw_s)
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

fn build_input(cases: &[(Vec<u32>, u32)]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (b, sval) in cases {
        s.push_str(&format!("{} {}\n", b.len(), sval));
        let parts: Vec<String> = b.iter().map(|x| x.to_string()).collect();
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

fn random_distinct_b(rng: &mut Rng, n: usize, max_val: u32) -> Vec<u32> {
    let mut s: HashSet<u32> = HashSet::new();
    let mut v: Vec<u32> = Vec::new();
    while v.len() < n {
        let x = rng.gen_range_u32(1, max_val);
        if s.insert(x) { v.push(x); }
    }
    v
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(0x1759B);
    let mut seen: HashSet<String> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;
    let mut tries = 0;
    while count < target && tries < target * 100 {
        tries += 1;
        let t = rng.gen_range_usize(1, 5);
        let mut cases: Vec<(Vec<u32>, u32)> = Vec::new();
        for _ in 0..t {
            let m = match tries % 4 {
                0 => rng.gen_range_usize(1, 5),
                1 => rng.gen_range_usize(1, 10),
                2 => rng.gen_range_usize(10, 30),
                _ => rng.gen_range_usize(20, 50),
            };
            let b = random_distinct_b(&mut rng, m, 50);
            let sv = rng.gen_range_u32(1, 1000);
            // Optionally tune to match: with 50% prob, set s to make it solvable
            let final_s = if rng.next_u64() % 2 == 0 {
                sv
            } else {
                // try to find a target that makes it solvable
                let sum_b: u32 = b.iter().sum();
                let max_b: u32 = *b.iter().max().unwrap();
                let candidates: Vec<u32> = (max_b..=100).filter_map(|n| {
                    let nn = n as u64;
                    let total = nn * (nn + 1) / 2;
                    if total >= sum_b as u64 {
                        let s = total - sum_b as u64;
                        if s >= 1 && s <= 1000 { Some(s as u32) } else { None }
                    } else {
                        None
                    }
                }).collect();
                if candidates.is_empty() { sv } else {
                    candidates[(rng.next_u64() as usize) % candidates.len()]
                }
            };
            let (b2, _, s2) = generate_test_case(b, final_s);
            cases.push((b2, s2));
        }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<bool> = cases.iter().map(|(b, sv)| Solution::lost_permutation(b.clone(), b.len(), *sv)).collect();
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}
