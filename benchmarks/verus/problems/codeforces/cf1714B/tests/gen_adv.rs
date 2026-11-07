use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: usize, a: Vec<i32>) -> (result: (usize, Vec<i32>))
    requires
        n >= 1,
        n <= 200_000,
        a.len() == n,
        forall|i: int|
            #![trigger a[i]]
            0 <= i && i < n as int ==> 1 <= a[i] as int && a[i] as int <= n as int,
    ensures
        result.0 >= 1,
        result.0 <= 200_000,
        result.1.len() == result.0,
        forall|i: int|
            #![trigger result.1[i]]
            0 <= i && i < result.0 as int ==> 1 <= result.1[i] as int && result.1[i] as int <= result.0 as int,
{
    (n, a)
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
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let r = (hi as i64 - lo as i64 + 1) as u64;
        (lo as i64 + (self.next_u64() % r) as i64) as i32
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

type TC = Vec<i32>;

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
        let ans = Solution::min_prefix_removals(a.len(), a.clone());
        s.push_str(&format!("{}\n", ans));
    }
    s
}

fn gen_case(rng: &mut Rng, mode: usize) -> TC {
    match mode {
        0 => {
            // n=1
            vec![1i32]
        }
        1 => {
            // all same
            let n = rng.gen_range_usize(1, 50);
            vec![1i32; n]
        }
        2 => {
            // identity-like: all distinct
            let n = rng.gen_range_usize(1, 50);
            (1..=n as i32).collect()
        }
        3 => {
            // moderate-large random
            let n = rng.gen_range_usize(500, 2000);
            (0..n).map(|_| rng.gen_range_i32(1, n as i32)).collect()
        }
        4 => {
            // small random
            let n = rng.gen_range_usize(2, 20);
            (0..n).map(|_| rng.gen_range_i32(1, n as i32)).collect()
        }
        5 => {
            // exactly 2 distinct values
            let n = rng.gen_range_usize(2, 100);
            (0..n).map(|_| if rng.next_u64() % 2 == 0 { 1i32 } else { 2i32 }).collect()
        }
        6 => {
            // last n distinct, prefix repeated
            let n = rng.gen_range_usize(2, 100);
            let mut v: Vec<i32> = (1..=n as i32).collect();
            // duplicate beginning
            for i in 0..(n / 2).min(v.len()) {
                v[i] = ((i % n) + 1) as i32;
            }
            v
        }
        _ => {
            let n = rng.gen_range_usize(1, 200);
            (0..n).map(|_| rng.gen_range_i32(1, n as i32)).collect()
        }
    }
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(1714);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;
    let mut tries = 0usize;

    while count < target && tries < 100000 {
        tries += 1;
        let t: usize = if count % 5 == 0 { rng.gen_range_usize(2, 20) } else { 1 };
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

