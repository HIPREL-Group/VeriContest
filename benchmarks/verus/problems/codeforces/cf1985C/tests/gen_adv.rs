use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: Vec<u64>) -> (result: Vec<u64>)
    ensures
        1 <= result.len() <= 200000,
        forall|i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] <= 1000000000,
{
    let n = if values.len() < 1 { 1usize }
            else if values.len() > 200000 { 200000usize } else { values.len() };
    let limit = 1000000000;
    let mut result = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant
            1 <= n <= 200000,
            limit == 1000000000,
            0 <= i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < result.len() ==> 0 <= #[trigger] result[j] <= limit,
        decreases n - i,
    {
        let value = if i < values.len() { values[i] } else { 0 };
        let value = if value < 0 { 0 } else if value > limit { limit } else { value };
        result.push(value);
        i += 1;
    }
    result
}


pub fn generate_candidate(seed_a: Vec<u64>) -> (result: Vec<u64>)
    requires
        1 <= seed_a.len() <= 50,
        forall |i: int| 0 <= i < seed_a.len() ==> #[trigger] seed_a[i] <= 1_000_000_000u64,
    ensures
        1 <= result.len() <= 200_000,
        forall |i: int| 0 <= i < result.len() ==> #[trigger] result[i] <= 1_000_000_000u64,
{
    seed_a
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
    fn gen_range_u64(&mut self, lo: u64, hi: u64) -> u64 {
        let range = (hi as u128 - lo as u128 + 1) as u128;
        (lo as u128 + (self.next_u64() as u128 % range)) as u64
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

fn build_input(cases: &[Vec<u64>]) -> String {
    let mut s = format!("{}\n", cases.len());
    for a in cases {
        s.push_str(&format!("{}\n", a.len()));
        let parts: Vec<String> = a.iter().map(|x| x.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn build_output(answers: &[usize]) -> String {
    let mut s = String::new();
    for ans in answers {
        s.push_str(&format!("{}\n", ans));
    }
    s
}

fn gen_seed(rng: &mut Rng, mode: usize) -> Vec<u64> {
    let n = match mode % 5 {
        0 => rng.gen_range_usize(1, 5),
        1 => rng.gen_range_usize(2, 10),
        2 => rng.gen_range_usize(10, 25),
        3 => rng.gen_range_usize(25, 40),
        _ => rng.gen_range_usize(40, 50),
    };
    match mode % 6 {
        0 => (0..n).map(|_| rng.gen_range_u64(0, 1_000_000_000u64)).collect(),
        1 => vec![0u64; n],
        2 => (0..n).map(|_| rng.gen_range_u64(0, 100u64)).collect(),
        3 => (0..n).map(|i| if i == 0 { 0u64 } else { 1u64 << (i.min(50) as u64) }).collect(),
        4 => (0..n).map(|i| (i as u64) + 1).collect(),
        _ => (0..n).map(|_| rng.gen_range_u64(0, 1000u64)).collect(),
    }
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(0x1985C);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut count = 0usize;
    let mut seen = HashSet::new();

    while count < target {
        let t: usize = if count < 20 { 1 }
                       else if count < 80 { rng.gen_range_usize(2, 6) }
                       else if count < 150 { rng.gen_range_usize(3, 15) }
                       else { rng.gen_range_usize(5, 30) };
        let mut cases: Vec<Vec<u64>> = Vec::with_capacity(t);
        for sub in 0..t {
            let mode = (count + sub) % 8;
            let seed_a = gen_seed(&mut rng, mode);
            let a = generate_candidate(seed_a);
            cases.push(a);
        }
        let answers: Vec<usize> = cases.iter().map(|a| Solution::count_good_prefixes_fn(a.clone())).collect();
        let cases: Vec<_> = cases.iter().cloned().map(generate_test_case).collect();
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}
