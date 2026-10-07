use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    vals: &Vec<i32>,
) -> (out: (i32, Vec<i32>))
    requires
        2 <= n <= 200_000,
        vals.len() == n,
        forall|i: int| 0 <= i < vals.len() ==> 1 <= #[trigger] vals[i] <= 1000,
    ensures
        out.1.len() == n,
        2 <= out.1.len() <= 200_000,
        forall|i: int| 0 <= i < out.1.len() ==> 1 <= #[trigger] out.1[i] <= 1000,
{
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            result.len() == i,
            vals.len() == n,
            2 <= n <= 200_000,
            forall|k: int| 0 <= k < vals.len() ==> 1 <= #[trigger] vals[k] <= 1000,
            forall|k: int| 0 <= k < result.len() ==> 1 <= #[trigger] result[k] <= 1000,
        decreases n - i,
    {
        result.push(vals[i]);
        i = i + 1;
    }
    (n as i32, result)
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
        let ans = Solution::max_coprime_index_sum(a.clone());
        s.push_str(&format!("{}\n", ans));
    }
    s
}

fn gen_case(rng: &mut Rng, mode: usize) -> TC {
    match mode {
        0 => {
            // small random
            let n = rng.gen_range_usize(2, 10);
            (0..n).map(|_| rng.gen_range_i32(1, 1000)).collect()
        }
        1 => {
            // all same
            let n = rng.gen_range_usize(2, 100);
            let v = rng.gen_range_i32(1, 1000);
            vec![v; n]
        }
        2 => {
            // all even (no coprime, so -1 except v=1)
            let n = rng.gen_range_usize(2, 100);
            (0..n).map(|_| rng.gen_range_i32(1, 500) * 2).collect()
        }
        3 => {
            // all 1s
            let n = rng.gen_range_usize(2, 100);
            vec![1i32; n]
        }
        4 => {
            // moderate-large
            let n = rng.gen_range_usize(500, 2000);
            (0..n).map(|_| rng.gen_range_i32(1, 1000)).collect()
        }
        5 => {
            // 1000s only
            let n = rng.gen_range_usize(2, 100);
            (0..n).map(|_| 1000i32).collect()
        }
        _ => {
            let n = rng.gen_range_usize(2, 100);
            (0..n).map(|_| rng.gen_range_i32(1, 1000)).collect()
        }
    }
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(1742);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;
    let mut tries = 0usize;

    while count < target && tries < 100000 {
        tries += 1;
        // t <= 10 per problem
        let t: usize = if count % 4 == 0 { rng.gen_range_usize(2, 10) } else { 1 };
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

