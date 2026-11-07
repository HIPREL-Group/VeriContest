use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: Vec<i64>) -> (result: Vec<i64>)
    ensures
        2 <= result.len() <= 200000,
        forall|i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] <= 1000000000,
{
    let n = if values.len() < 2 { 2usize }
            else if values.len() > 200000 { 200000usize } else { values.len() };
    let limit = 1000000000;
    let mut result = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant
            2 <= n <= 200000,
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


pub fn generate_candidate(values: &Vec<i64>) -> (a: Vec<i64>)
    requires
        2 <= values.len() <= 200000,
        forall|i: int| 0 <= i < values.len() ==> 0 <= #[trigger] values[i] <= 1000000000,
    ensures
        2 <= a.len() <= 200000,
        forall|j: int| 0 <= j < a.len() as int ==> 0 <= #[trigger] a[j] as int <= 1000000000,
{
    let mut a: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    let n = values.len();
    while i < n
        invariant
            n == values.len(),
            0 <= i <= n,
            a.len() == i,
            forall|k: int| 0 <= k < values.len() ==> 0 <= #[trigger] values[k] <= 1000000000,
            forall|k: int| 0 <= k < i as int ==> a[k] == values[k],
        decreases n - i,
    {
        a.push(values[i]);
        i = i + 1;
    }
    a
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

type TC = Vec<i64>;

fn build_input(cases: &[TC]) -> String {
    let mut s = format!("{}\n", cases.len());
    for a in cases {
        s.push_str(&format!("{}\n", a.len()));
        let parts: Vec<String> = a.iter().map(|x| x.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn build_output(cases: &[TC]) -> String {
    let mut s = String::new();
    for a in cases {
        let ans = Solution::min_operations(a.clone());
        s.push_str(&format!("{}\n", ans));
    }
    s
}

fn gen_case(rng: &mut Rng, mode: usize) -> TC {
    match mode {
        0 => {
            // small, all zero
            let n = rng.gen_range_usize(1, 10);
            vec![0i64; n]
        }
        1 => {
            // small, all max
            let n = rng.gen_range_usize(1, 10);
            vec![1_000_000_000i64; n]
        }
        2 => {
            // single element
            vec![rng.gen_range_i64(0, 1_000_000_000)]
        }
        3 => {
            // mostly zeros with a bunch in front
            let n = rng.gen_range_usize(2, 100);
            let mut v = vec![0i64; n];
            v[0] = rng.gen_range_i64(0, 1_000_000_000);
            v
        }
        4 => {
            // mostly zeros with last big
            let n = rng.gen_range_usize(2, 100);
            let mut v = vec![0i64; n];
            v[n-1] = rng.gen_range_i64(0, 1_000_000_000);
            v
        }
        5 => {
            // alternating
            let n = rng.gen_range_usize(2, 200);
            (0..n).map(|i| if i % 2 == 0 { rng.gen_range_i64(0, 1_000_000_000) } else { 0 }).collect()
        }
        6 => {
            // random small
            let n = rng.gen_range_usize(1, 200);
            (0..n).map(|_| rng.gen_range_i64(0, 100)).collect()
        }
        7 => {
            // moderate-large
            let n = rng.gen_range_usize(500, 2000);
            (0..n).map(|_| rng.gen_range_i64(0, 1_000_000_000)).collect()
        }
        _ => {
            let n = rng.gen_range_usize(1, 50);
            (0..n).map(|_| rng.gen_range_i64(0, 1_000_000_000)).collect()
        }
    }
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(1705);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;
    let mut tries = 0usize;

    while count < target && tries < 100000 {
        tries += 1;
        let t: usize = if count % 5 == 0 { rng.gen_range_usize(2, 15) } else { 1 };
        let mut cases: Vec<TC> = Vec::new();
        for _ in 0..t {
            let mode = (rng.next_u64() as usize) % 9;
            cases.push(gen_case(&mut rng, mode));
        }
        let cases: Vec<_> = cases.iter().cloned().map(generate_test_case).collect();
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let outs = build_output(&cases);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}
