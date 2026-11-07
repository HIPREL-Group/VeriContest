use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    period: u32,
    offset: i32,
    perm: &Vec<usize>,
) -> (result: (Vec<i32>, u32))
    requires
        1 <= n <= 200_000,
        1 <= period as int <= n as int,
        1 <= offset <= 1_000_000_000 - n as i32,
        perm.len() == n,
        forall|i: int| 0 <= i < perm.len() ==> #[trigger] perm[i] < n,
    ensures
        result.0.len() == n,
        result.0.len() >= 1,
        result.0.len() <= 200_000,
        1 <= result.1 as int,
        result.1 as int <= result.0.len() as int,
        result.1 == period,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 1_000_000_000,
{
    let mut a: Vec<i32> = Vec::new();
    let mut idx: usize = 0;
    while idx < n
        invariant
            a.len() == idx,
            idx <= n,
            1 <= n <= 200_000,
            1 <= offset <= 1_000_000_000 - n as i32,
            perm.len() == n,
            forall|i: int| 0 <= i < perm.len() ==> #[trigger] perm[i] < n,
            forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= 1_000_000_000,
        decreases n - idx,
    {
        let p = perm[idx];
        assert(p < n);
        let v: i32 = offset + (p as i32);
        assert(v >= 1);
        assert(v <= 1_000_000_000);
        a.push(v);
        idx = idx + 1;
    }
    (a, period)
}

}

use std::io::Write;
use std::collections::HashSet;

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }

    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0
    }

    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
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

fn build_input_multi(cases: &[(Vec<i32>, u32)]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (a, k) in cases {
        s.push_str(&format!("{} {}\n", a.len(), k));
        let parts: Vec<String> = a.iter().map(|x| x.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn build_output_multi(answers: &[i32]) -> String {
    let mut s = String::new();
    for ans in answers {
        s.push_str(&format!("{}\n", ans));
    }
    s
}

fn make_distinct(rng: &mut Rng, n: usize, lo: i64, hi: i64) -> Vec<i32> {
    let mut used = HashSet::new();
    let mut a: Vec<i32> = Vec::with_capacity(n);
    let mut tries = 0;
    let max_tries = n * 30 + 100;
    while a.len() < n && tries < max_tries {
        tries += 1;
        let v = rng.gen_range_i64(lo, hi) as i32;
        if used.insert(v) { a.push(v); }
    }
    a
}

fn gen_mode(rng: &mut Rng, mode: usize) -> (Vec<i32>, u32) {
    match mode {
        0 => {
            // small case
            let n = rng.gen_range_usize(1, 5);
            let k = rng.gen_range_usize(1, n) as u32;
            let max_a = (n * 20 + 30) as i64;
            (make_distinct(rng, n, 1, max_a), k)
        }
        1 => {
            // n=1, varied k
            let k = rng.gen_range_usize(1, 1) as u32;
            (vec![rng.gen_range_i64(1, 100) as i32], k)
        }
        2 => {
            // larger k
            let n = rng.gen_range_usize(2, 10);
            let k = n as u32;
            let max_a = (n * 30 + 50) as i64;
            (make_distinct(rng, n, 1, max_a), k)
        }
        3 => {
            // k=1
            let n = rng.gen_range_usize(1, 20);
            let max_a = (n * 5 + 20) as i64;
            (make_distinct(rng, n, 1, max_a), 1u32)
        }
        4 => {
            // contiguous a values
            let n = rng.gen_range_usize(2, 30);
            let k = rng.gen_range_usize(1, n) as u32;
            let start = rng.gen_range_i64(1, 1000) as i32;
            let mut a: Vec<i32> = (0..n as i32).map(|i| start + i).collect();
            // shuffle a bit
            for i in (1..n).rev() {
                let j = rng.gen_range_usize(0, i);
                a.swap(i, j);
            }
            (a, k)
        }
        5 => {
            // adversarial: spread values
            let n = rng.gen_range_usize(2, 20);
            let k = rng.gen_range_usize(1, n) as u32;
            let max_a = (n * 100 + 1000) as i64;
            (make_distinct(rng, n, 1, max_a), k)
        }
        6 => {
            // moderate medium
            let n = rng.gen_range_usize(20, 80);
            let k = rng.gen_range_usize(1, n) as u32;
            let max_a = (n * 30 + 50) as i64;
            (make_distinct(rng, n, 1, max_a), k)
        }
        7 => {
            // edge: a values close together
            let n = rng.gen_range_usize(2, 15);
            let k = rng.gen_range_usize(1, n) as u32;
            let start = rng.gen_range_i64(100, 10000) as i32;
            let mut s = HashSet::new();
            let mut a = Vec::new();
            while a.len() < n {
                let off = rng.gen_range_i64(0, (n * 3) as i64) as i32;
                let v = start + off;
                if s.insert(v) { a.push(v); }
            }
            (a, k)
        }
        8 => {
            // a values with k matching n
            let n = rng.gen_range_usize(2, 20);
            let k = n as u32;
            let max_a = (n * 30 + 50) as i64;
            (make_distinct(rng, n, 1, max_a), k)
        }
        _ => {
            let n = rng.gen_range_usize(1, 50);
            let k = rng.gen_range_usize(1, n) as u32;
            let max_a = (n * 30 + 50) as i64;
            (make_distinct(rng, n, 1, max_a), k)
        }
    }
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(1);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut count = 0usize;
    let modes = 10usize;

    while count < target {
        let t: usize = if count < 20 { 1 }
                       else if count < 80 { rng.gen_range_usize(2, 6) }
                       else if count < 150 { rng.gen_range_usize(3, 12) }
                       else { rng.gen_range_usize(5, 25) };

        let mut cases: Vec<(Vec<i32>, u32)> = Vec::new();
        let mut total_n = 0usize;
        for sub in 0..t {
            let mode = (count * 7 + sub) % modes;
            let (a, k) = gen_mode(&mut rng, mode);
            if a.is_empty() { continue; }
            if total_n + a.len() > 500 { break; }
            total_n += a.len();
            cases.push((a, k));
        }
        if cases.is_empty() { continue; }
        let key = format!("{:?}", cases);
        if !seen.insert(key) { continue; }
        let answers: Vec<i32> = cases.iter().map(|(a, k)| Solution::light_switches(a.clone(), *k)).collect();
        let inp = build_input_multi(&cases);
        let outp = build_output_multi(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

