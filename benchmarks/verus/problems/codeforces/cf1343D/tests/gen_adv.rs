use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    k: i64,
    a: Vec<i64>,
) -> (res: (usize, i64, Vec<i64>))
    requires
        2 <= n && n <= 200000,
        n % 2 == 0,
        1 <= k && k <= 200000,
        a.len() == n,
        forall|i: int| 0 <= i && i < n ==> 1 <= a@[i] && a@[i] <= k,
    ensures
        ({
            let (nn, kk, aa) = res;
            &&& 2 <= nn && nn <= 200000
            &&& nn % 2 == 0
            &&& 1 <= kk && kk <= 200000
            &&& aa.len() == nn
            &&& forall|i: int| 0 <= i && i < nn ==> 1 <= aa@[i] && aa@[i] <= kk
        }),
{
    (n, k, a)
}

pub fn clamp_value(v: i64, k: i64) -> (r: i64)
    requires 1 <= k,
    ensures 1 <= r && r <= k,
{
    if v < 1 { 1 }
    else if v > k { k }
    else { v }
}

pub fn build_array(n: usize, k: i64, raw: Vec<i64>) -> (a: Vec<i64>)
    requires
        1 <= k && k <= 200000,
        raw.len() == n,
    ensures
        a.len() == n,
        forall|i: int| 0 <= i && i < n ==> 1 <= a@[i] && a@[i] <= k,
{
    let mut a: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            1 <= k && k <= 200000,
            raw.len() == n,
            a.len() == i,
            i <= n,
            forall|j: int| 0 <= j && j < i ==> 1 <= a@[j] && a@[j] <= k,
        decreases n - i,
    {
        let v = clamp_value(raw[i], k);
        a.push(v);
        i = i + 1;
    }
    a
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

fn make_even(n: usize) -> usize { if n % 2 == 0 { n } else { n + 1 } }

fn build_input(cases: &[(usize, i64, Vec<i64>)]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (n, k, a) in cases {
        s.push_str(&format!("{} {}\n", n, k));
        let parts: Vec<String> = a.iter().map(|x| x.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn build_output(answers: &[i64]) -> String {
    let mut s = String::new();
    for a in answers {
        s.push_str(&format!("{}\n", a));
    }
    s
}

fn gen_case(rng: &mut Rng, mode: usize) -> (usize, i64, Vec<i64>) {
    let (n_raw, k): (usize, i64) = match mode {
        0 => (2, rng.gen_range_i64(1, 10)),
        1 => (rng.gen_range_usize(2, 20), rng.gen_range_i64(1, 20)),
        2 => (rng.gen_range_usize(2, 100), rng.gen_range_i64(1, 100)),
        3 => (200, 200),
        4 => (2, 200000),
        5 => (rng.gen_range_usize(2, 1000), rng.gen_range_i64(1, 1000)),
        6 => {
            let k = rng.gen_range_i64(2, 50);
            (rng.gen_range_usize(2, 50), k)
        }
        7 => (4, rng.gen_range_i64(1, 5)),
        8 => (rng.gen_range_usize(2, 100), 2),
        9 => (rng.gen_range_usize(2, 500), rng.gen_range_i64(1, 500)),
        10 => (rng.gen_range_usize(2, 5000), rng.gen_range_i64(1, 5000)),
        _ => (rng.gen_range_usize(2, 200), rng.gen_range_i64(1, 200)),
    };
    let n = make_even(n_raw.max(2).min(20000));
    let k = k.max(1).min(20000);
    let mut raw: Vec<i64> = Vec::with_capacity(n);
    match mode {
        0 => { for _ in 0..n { raw.push(1); } }
        3 => { for _ in 0..n { raw.push(k); } }
        7 => {
            for _ in 0..n/2 {
                let v = rng.gen_range_i64(1, k);
                raw.push(v);
            }
            for i in 0..n/2 {
                let idx = n/2 - 1 - i;
                raw.push(raw[idx]);
            }
        }
        8 => {
            for i in 0..n {
                if i % 2 == 0 { raw.push(1); } else { raw.push(k); }
            }
        }
        _ => {
            for _ in 0..n { raw.push(rng.gen_range_i64(1, k)); }
        }
    }
    while raw.len() < n { raw.push(1); }
    while raw.len() > n { raw.pop(); }
    let a: Vec<i64> = raw.into_iter().map(|v| v.max(1).min(k)).collect();
    (n, k, a)
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(31337);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);

    {
        let cases: Vec<(usize, i64, Vec<i64>)> = vec![
            (4, 2, vec![1, 2, 1, 2]),
            (4, 3, vec![1, 2, 2, 1]),
            (8, 7, vec![6, 1, 1, 7, 6, 3, 4, 6]),
            (6, 6, vec![5, 2, 6, 1, 3, 4]),
        ];
        let answers: Vec<i64> = cases.iter().map(|(n, k, a)| Solution::constant_palindrome_sum(*n, *k, a.clone())).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
    }

    let mut count = 1usize;
    let modes = 12usize;
    while count < target {
        let mode = count % modes;
        let bundle_size: usize = if count < 20 { 1 }
            else if count < 60 { rng.gen_range_usize(2, 5) }
            else if count < 120 { rng.gen_range_usize(5, 15) }
            else { rng.gen_range_usize(10, 50) };
        let mut cases: Vec<(usize, i64, Vec<i64>)> = Vec::new();
        let mut answers: Vec<i64> = Vec::new();
        for _ in 0..bundle_size {
            let (n, k, a) = gen_case(&mut rng, mode);
            let ans = Solution::constant_palindrome_sum(n, k, a.clone());
            cases.push((n, k, a));
            answers.push(ans);
        }
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

