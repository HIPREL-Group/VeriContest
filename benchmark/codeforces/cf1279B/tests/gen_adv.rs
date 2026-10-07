use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    s: i64,
    fillers: &Vec<i64>,
) -> (res: (usize, i64, Vec<i64>))
    requires
        1 <= n <= 100000,
        fillers.len() == n,
        1 <= s <= 1_000_000_000,
        forall|i: int| 0 <= i < fillers.len() ==>
            1 <= #[trigger] fillers[i] <= 1_000_000_000,
    ensures
        ({
            let (nn, ss, a) = res;
            &&& 1 <= nn <= 100000
            &&& a.len() == nn
            &&& 1 <= ss <= 1_000_000_000
            &&& forall|i: int| #![trigger a[i]] 0 <= i < nn as int ==> 1 <= a[i] && a[i] <= 1_000_000_000
        }),
{
    let mut a: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == fillers.len(),
            0 <= i <= n,
            a.len() == i,
            forall|k: int| 0 <= k < i as int ==> #[trigger] a[k] == fillers[k],
            forall|k: int| 0 <= k < fillers.len() ==> 1 <= #[trigger] fillers[k] <= 1_000_000_000,
        decreases n - i,
    {
        a.push(fillers[i]);
        i = i + 1;
    }
    (n, s, a)
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

fn build_input(cases: &[(i64, Vec<i64>)]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (sv, a) in cases {
        s.push_str(&format!("{} {}\n", a.len(), sv));
        let parts: Vec<String> = a.iter().map(|x| x.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn build_output(answers: &[i32]) -> String {
    let mut s = String::new();
    for a in answers { s.push_str(&format!("{}\n", a)); }
    s
}

fn random_array(rng: &mut Rng, len: usize, max_val: i64) -> Vec<i64> {
    (0..len).map(|_| rng.gen_range_i64(1, max_val)).collect()
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(987654321);
    let mut seen: HashSet<u64> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |cases: Vec<(i64, Vec<i64>)>, seen: &mut HashSet<u64>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if cases.iter().any(|(_, a)| a.is_empty()) { return; }
        let mut h: u64 = 1469598103934665603;
        h ^= cases.len() as u64; h = h.wrapping_mul(1099511628211);
        for (sv, a) in &cases {
            h ^= *sv as u64; h = h.wrapping_mul(1099511628211);
            h ^= a.len() as u64; h = h.wrapping_mul(1099511628211);
            for &x in a { h ^= x as u64; h = h.wrapping_mul(1099511628211); }
        }
        if !seen.insert(h) { return; }
        let answers: Vec<i32> = cases.iter().map(|(sv, a)| Solution::verse_for_santa(a.len(), *sv, a.clone())).collect();
        let inp = build_input(&cases);
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    // Patterns
    for &n in &[1usize, 2, 5, 10, 100, 1000, 10_000, 50_000] {
        emit(vec![(1_000_000_000i64, vec![1; n])], &mut seen, &mut out, &mut count);
        emit(vec![(1i64, vec![1; n])], &mut seen, &mut out, &mut count);
        emit(vec![(n as i64, vec![1; n])], &mut seen, &mut out, &mut count);
        let v: Vec<i64> = (0..n).map(|i| (i + 1) as i64).collect();
        emit(vec![(n as i64, v)], &mut seen, &mut out, &mut count);
    }

    let mut tries = 0;
    while count < target && tries < 5000 {
        tries += 1;
        let t: usize = match tries % 5 {
            0 => 1,
            1 => rng.gen_range_usize(2, 10),
            2 => rng.gen_range_usize(10, 50),
            3 => rng.gen_range_usize(50, 100),
            _ => rng.gen_range_usize(2, 20),
        };
        let mut cases: Vec<(i64, Vec<i64>)> = Vec::new();
        let mut total_n = 0usize;
        for _ in 0..t {
            if total_n >= 80_000 { break; }
            let max_n = (100_000 - total_n).min(10_000);
            let n = match tries % 6 {
                0 => rng.gen_range_usize(1, 5),
                1 => rng.gen_range_usize(5, 50),
                2 => rng.gen_range_usize(50, 500),
                3 => rng.gen_range_usize(500, 5_000),
                4 => rng.gen_range_usize(5_000, max_n.max(5_000)),
                _ => rng.gen_range_usize(1, 100),
            };
            total_n += n;
            let max_a = match tries % 4 {
                0 => 10i64,
                1 => 1000,
                2 => 100_000,
                _ => 1_000_000_000,
            };
            let a = random_array(&mut rng, n, max_a);
            let sv = rng.gen_range_i64(1, 1_000_000_000);
            cases.push((sv, a));
        }
        if !cases.is_empty() {
            emit(cases, &mut seen, &mut out, &mut count);
        }
    }
}

