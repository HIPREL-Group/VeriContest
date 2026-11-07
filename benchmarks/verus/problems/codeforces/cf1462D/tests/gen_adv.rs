use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    vals: &Vec<i64>,
) -> (result: (usize, Vec<i64>))
    requires
        1 <= n <= 3000,
        vals.len() == n,
        forall|i: int| 0 <= i < n as int ==> 1 <= (#[trigger] vals[i]) <= 100000,
    ensures
        result.0 == n,
        1 <= result.0 <= 3000,
        result.1.len() == n,
        forall|i: int| 0 <= i < n as int ==> 1 <= (#[trigger] result.1[i]) <= 100000,
{
    let mut a: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            a.len() == i,
            vals.len() == n,
            forall|k: int| 0 <= k < n as int ==> 1 <= (#[trigger] vals[k]) <= 100000,
            forall|k: int| 0 <= k < i as int ==> 1 <= (#[trigger] a[k]) <= 100000,
        decreases n - i,
    {
        a.push(vals[i]);
        i = i + 1;
    }
    (n, a)
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

fn build_output(answers: &[i64]) -> String {
    let mut s = String::new();
    for &a in answers {
        s.push_str(&format!("{}\n", a));
    }
    s
}

fn gen_arr(rng: &mut Rng, n: usize, mode: u64) -> Vec<i64> {
    let mut a: Vec<i64> = Vec::with_capacity(n);
    match mode {
        0 => for _ in 0..n { a.push(1); },
        1 => for _ in 0..n { a.push(rng.gen_range_i64(1, 5)); }, // small
        2 => for _ in 0..n { a.push(100000); },
        3 => for i in 0..n { a.push((i + 1) as i64); }, // increasing
        4 => { // sum divisible by k
            let v = rng.gen_range_i64(1, 100);
            for _ in 0..n { a.push(v); }
        }
        _ => for _ in 0..n { a.push(rng.gen_range_i64(1, 100000)); },
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
        let mut a = Vec::new();
        for i in 0..500 { a.push(((i % 10) + 1) as i64); }
        let cases: Vec<Vec<i64>> = vec![a];
        let answers: Vec<i64> = cases.iter().map(|a| Solution::min_operations(a.len(), a.clone())).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }

    while count < target {
        let t: usize = match count % 5 {
            0 => 1,
            1 => rng.gen_range_usize(2, 5),
            2 => rng.gen_range_usize(5, 20),
            3 => rng.gen_range_usize(20, 50),
            _ => rng.gen_range_usize(50, 100),
        };
        let mut cases: Vec<Vec<i64>> = Vec::new();
        let mut total = 0;
        for _ in 0..t {
            let n = match rng.next_u64() % 5 {
                0 => 1,
                1 => rng.gen_range_usize(1, 5),
                2 => rng.gen_range_usize(5, 30),
                3 => rng.gen_range_usize(30, 100),
                _ => rng.gen_range_usize(100, 300),
            };
            if total + n > 1500 { break; }
            total += n;
            let mode = rng.next_u64() % 6;
            cases.push(gen_arr(&mut rng, n, mode));
        }
        if cases.is_empty() { continue; }
        let answers: Vec<i64> = cases.iter().map(|a| Solution::min_operations(a.len(), a.clone())).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

