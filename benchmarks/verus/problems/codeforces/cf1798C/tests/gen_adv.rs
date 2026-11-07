use vstd::prelude::*;

verus! {

pub fn generate_test_case(raw_a: Vec<i64>, raw_b: Vec<i64>) -> (result: (usize, Vec<i64>, Vec<i64>))
    ensures
        2 <= result.1.len() <= 200000,
        result.1.len() == result.2.len(),
        result.0 == result.1.len(),
        forall|j: int| 0 <= j < result.1.len() ==> 1 <= #[trigger] result.1[j] <= 1000000000,
        forall|j: int| 0 <= j < result.2.len() ==> 1 <= #[trigger] result.2[j] <= 10000,
{
    let n = if raw_a.len() < 2 { 2usize } else if raw_a.len() > 200000 { 200000usize } else { raw_a.len() };
    let mut a: Vec<i64> = Vec::new();
    let mut b: Vec<i64> = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant
            2 <= n <= 200000, 0 <= i <= n, a.len() == i, b.len() == i,
            forall|j: int| 0 <= j < a.len() ==> 1 <= #[trigger] a[j] <= 1000000000,
            forall|j: int| 0 <= j < b.len() ==> 1 <= #[trigger] b[j] <= 10000,
        decreases n - i,
    {
        let av = if i < raw_a.len() { raw_a[i] } else { 1 };
        let bv = if i < raw_b.len() { raw_b[i] } else { 1 };
        a.push(if av < 1 { 1 } else if av > 1000000000 { 1000000000 } else { av });
        b.push(if bv < 1 { 1 } else if bv > 10000 { 10000 } else { bv });
        i += 1;
    }
    (n, a, b)
}


pub fn generate_candidate(
    a_vals: &Vec<i64>,
    b_vals: &Vec<i64>,
) -> (result: (Vec<i64>, Vec<i64>))
    requires
        a_vals.len() == b_vals.len(),
        1 <= a_vals.len() <= 200_000,
        forall|i: int| 0 <= i < a_vals.len() ==> 1 <= #[trigger] a_vals[i] <= 1_000_000_000,
        forall|i: int| 0 <= i < b_vals.len() ==> 1 <= #[trigger] b_vals[i] <= 10_000,
    ensures
        result.0.len() == result.1.len(),
        1 <= result.0.len() <= 200_000,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 1_000_000_000,
        forall|i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i] <= 10_000,
{
    let mut a_out: Vec<i64> = Vec::new();
    let mut b_out: Vec<i64> = Vec::new();

    let n = a_vals.len();
    let mut i: usize = 0;
    while i < n
        invariant
            n == a_vals.len(),
            a_vals.len() == b_vals.len(),
            1 <= a_vals.len() <= 200_000,
            0 <= i <= n,
            a_out.len() == i,
            b_out.len() == i,
            forall|k: int| 0 <= k < i as int ==> #[trigger] a_out[k] == a_vals[k],
            forall|k: int| 0 <= k < i as int ==> #[trigger] b_out[k] == b_vals[k],
            forall|k: int| 0 <= k < a_vals.len() ==> 1 <= #[trigger] a_vals[k] <= 1_000_000_000,
            forall|k: int| 0 <= k < b_vals.len() ==> 1 <= #[trigger] b_vals[k] <= 10_000,
        decreases n - i,
    {
        a_out.push(a_vals[i]);
        b_out.push(b_vals[i]);
        i = i + 1;
    }

    (a_out, b_out)
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

type TC = (usize, Vec<i64>, Vec<i64>);

fn build_input(cases: &[TC]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (n, a, b) in cases {
        s.push_str(&format!("{}\n", n));
        for i in 0..*n {
            s.push_str(&format!("{} {}\n", a[i], b[i]));
        }
    }
    s
}

fn build_output(cases: &[TC]) -> String {
    let mut s = String::new();
    for (_n, a, b) in cases {
        let ans = Solution::min_tags(a.clone(), b.clone());
        s.push_str(&format!("{}\n", ans));
    }
    s
}

fn gen_case(rng: &mut Rng, mode: usize) -> TC {
    match mode {
        0 => {
            // n=1
            let a = vec![rng.gen_range_i64(1, 1_000_000)];
            let b = vec![rng.gen_range_i64(1, 1_000_000)];
            (1, a, b)
        }
        1 => {
            // all b same -> 1 tag
            let n = rng.gen_range_usize(1, 100);
            let bv = rng.gen_range_i64(1, 100);
            let a: Vec<i64> = (0..n).map(|_| rng.gen_range_i64(1, 1000)).collect();
            let b: Vec<i64> = vec![bv; n];
            // Note: even with same b, tags depends on whether c values can be made equal
            (n, a, b)
        }
        2 => {
            // a_i = b_i = i
            let n = rng.gen_range_usize(1, 100);
            let a: Vec<i64> = (1..=n as i64).collect();
            let b: Vec<i64> = (1..=n as i64).collect();
            (n, a, b)
        }
        3 => {
            // small random with small values
            let n = rng.gen_range_usize(2, 30);
            let a: Vec<i64> = (0..n).map(|_| rng.gen_range_i64(1, 20)).collect();
            let b: Vec<i64> = (0..n).map(|_| rng.gen_range_i64(1, 20)).collect();
            (n, a, b)
        }
        4 => {
            // moderate-large random
            let n = rng.gen_range_usize(100, 500);
            let a: Vec<i64> = (0..n).map(|_| rng.gen_range_i64(1, 1_000_000)).collect();
            let b: Vec<i64> = (0..n).map(|_| rng.gen_range_i64(1, 1_000_000)).collect();
            (n, a, b)
        }
        _ => {
            let n = rng.gen_range_usize(1, 100);
            let a: Vec<i64> = (0..n).map(|_| rng.gen_range_i64(1, 1000)).collect();
            let b: Vec<i64> = (0..n).map(|_| rng.gen_range_i64(1, 1000)).collect();
            (n, a, b)
        }
    }
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(1798);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;
    let mut tries = 0usize;

    while count < target && tries < 100000 {
        tries += 1;
        let t: usize = if count % 5 == 0 { rng.gen_range_usize(2, 30) } else { 1 };
        let mut cases: Vec<TC> = Vec::new();
        for _ in 0..t {
            let mode = (rng.next_u64() as usize) % 6;
            cases.push(gen_case(&mut rng, mode));
        }
        let cases: Vec<_> = cases.iter().map(|c| generate_test_case(c.1.clone(), c.2.clone())).collect();
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let outs = build_output(&cases);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}
