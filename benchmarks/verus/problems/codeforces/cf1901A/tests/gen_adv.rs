use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    x: i64,
    a: Vec<i64>,
) -> (res: (i64, Vec<i64>))
    requires
        1 <= a.len() <= 50,
        2 <= x <= 100,
        forall|j: int|
            0 <= j < a.len() as int - 1 ==> (#[trigger] a[j] as int) < (a[j + 1] as int),
        forall|j: int|
            0 <= j < a.len() as int ==> 0 < #[trigger] a[j] as int && (a[j] as int) < x as int,
    ensures
        1 <= res.1.len() <= 50,
        2 <= res.0 <= 100,
        forall|j: int|
            0 <= j < res.1.len() as int - 1 ==> (#[trigger] res.1[j] as int) < (res.1[j + 1] as int),
        forall|j: int|
            0 <= j < res.1.len() as int ==> 0 < #[trigger] res.1[j] as int && (res.1[j] as int) < res.0 as int,
{
    (x, a)
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

type Case = (i64, Vec<i64>);

fn build_input(cases: &[Case]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (x, a) in cases {
        s.push_str(&format!("{} {}\n", a.len(), x));
        let p: Vec<String> = a.iter().map(|v| v.to_string()).collect();
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

fn solve(c: &Case) -> i64 {
    Solution::min_tank_liters(c.0, c.1.clone())
}

fn random_case(rng: &mut Rng) -> Case {
    let x = rng.gen_range_i64(2, 100);
    let max_n = (x - 1).min(50);
    if max_n < 1 { return (x, vec![1]); }
    let n = rng.gen_range_i64(1, max_n) as usize;
    let mut chosen: Vec<i64> = Vec::with_capacity(n);
    let mut available: Vec<i64> = (1..x).collect();
    for _ in 0..n {
        let idx = (rng.next_u64() as usize) % available.len();
        chosen.push(available.swap_remove(idx));
    }
    chosen.sort();
    (x, chosen)
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
        let mut cases: Vec<Case> = Vec::new();
        for _ in 0..t {
            cases.push(random_case(&mut rng));
        }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<i64> = cases.iter().map(|c| solve(c)).collect();
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}

