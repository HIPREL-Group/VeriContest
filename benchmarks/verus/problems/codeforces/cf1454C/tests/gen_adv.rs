use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: usize, vals: &Vec<i64>) -> (result: Vec<i64>)
    requires
        1 <= n <= 200_000,
        vals.len() == n,
        forall |k: int| 0 <= k < vals.len() ==> 1 <= #[trigger] vals[k] <= n as i64,
    ensures
        1 <= result.len() <= 200_000,
        result.len() == n,
        forall |k: int| 0 <= k < result.len() ==> 1 <= #[trigger] result[k] <= result.len() as i64,
{
    let mut out: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            1 <= n <= 200_000,
            vals.len() == n,
            0 <= i <= n,
            out.len() == i,
            forall |k: int| 0 <= k < vals.len() ==> 1 <= #[trigger] vals[k] <= n as i64,
            forall |k: int| 0 <= k < out.len() ==> #[trigger] out[k] == vals[k],
        decreases n - i,
    {
        out.push(vals[i]);
        i = i + 1;
    }
    assert(out.len() == n);
    assert forall |k: int| 0 <= k < out.len() implies 1 <= #[trigger] out[k] <= out.len() as i64 by {
        assert(out[k] == vals[k]);
        assert(1 <= vals[k] <= n as i64);
    }
    out
}

}

use std::io::Write;

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

fn build_input(cases: &[Vec<i64>]) -> String {
    let mut s = format!("{}\n", cases.len());
    for a in cases {
        s.push_str(&format!("{}\n", a.len()));
        let parts: Vec<String> = a.iter().map(|x| x.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn build_output(answers: &[u64]) -> String {
    let mut s = String::new();
    for &a in answers {
        s.push_str(&format!("{}\n", a));
    }
    s
}

fn gen_arr(rng: &mut Rng, n: usize, mode: u64) -> Vec<i64> {
    let mut a: Vec<i64> = Vec::with_capacity(n);
    let max_val = (n as i64).max(1);
    match mode {
        0 => for _ in 0..n { a.push(1); },
        1 => for _ in 0..n { a.push(max_val); },
        2 => for i in 0..n { a.push((i as i64 % max_val) + 1); },
        3 => { // alternating two values
            for i in 0..n { a.push(((i & 1) + 1) as i64); }
        }
        4 => { // single rare elem
            for _ in 0..n { a.push(1); }
            if n > 0 { a[n / 2] = max_val; }
        }
        _ => for _ in 0..n { a.push(rng.gen_range_i64(1, max_val)); },
    }
    a
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(31337);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);

    let mut count = 0usize;

    // Big single
    {
        let cases: Vec<Vec<i64>> = vec![(1..=2000).collect()];
        let answers: Vec<u64> = cases.iter().map(|a| Solution::min_ops(a.clone())).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }

    while count < target {
        let t: usize = match count % 5 {
            0 => 1,
            1 => rng.gen_range_usize(2, 10),
            2 => rng.gen_range_usize(10, 50),
            3 => rng.gen_range_usize(50, 200),
            _ => rng.gen_range_usize(200, 1000),
        };
        let mut cases: Vec<Vec<i64>> = Vec::new();
        let mut total = 0;
        for _ in 0..t {
            let n = match rng.next_u64() % 5 {
                0 => 1,
                1 => rng.gen_range_usize(1, 5),
                2 => rng.gen_range_usize(5, 30),
                3 => rng.gen_range_usize(30, 200),
                _ => rng.gen_range_usize(200, 1000),
            };
            if total + n > 50000 { break; }
            total += n;
            let mode = rng.next_u64() % 6;
            cases.push(gen_arr(&mut rng, n, mode));
        }
        if cases.is_empty() { continue; }
        let answers: Vec<u64> = cases.iter().map(|a| Solution::min_ops(a.clone())).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

