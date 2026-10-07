use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (result: Vec<i32>)
    requires
        1 <= values.len() <= 150_000,
        forall |k: int| 0 <= k < values.len() ==> 1 <= (#[trigger] values[k]) <= 1_000_000,
    ensures
        1 <= result.len() <= 150_000,
        forall |k: int| 0 <= k < result.len() ==> 1 <= (#[trigger] result[k]) <= 1_000_000,
{
    let mut result: Vec<i32> = Vec::new();
    let n = values.len();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == values.len(),
            result.len() == i,
            forall |k: int| 0 <= k < values.len() ==> 1 <= (#[trigger] values[k]) <= 1_000_000,
            forall |k: int| 0 <= k < i as int ==> 1 <= (#[trigger] result[k]) <= 1_000_000,
            forall |k: int| 0 <= k < i as int ==> #[trigger] result[k] == values[k],
        decreases n - i,
    {
        result.push(values[i]);
        i += 1;
    }
    result
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
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let r = (hi as i64 - lo as i64 + 1) as u64;
        (lo as i64 + (self.next_u64() as u64 % r) as i64) as i32
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

fn build_input(cases: &[Vec<i32>]) -> String {
    let mut s = format!("{}\n", cases.len());
    for case in cases {
        s.push_str(&format!("{}\n", case.len()));
        let parts: Vec<String> = case.iter().map(|x| x.to_string()).collect();
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

fn random_array(rng: &mut Rng, len: usize, max_val: i32) -> Vec<i32> {
    (0..len).map(|_| rng.gen_range_i32(1, max_val)).collect()
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(987654321);
    let mut seen: HashSet<u64> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |cases: Vec<Vec<i32>>, seen: &mut HashSet<u64>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if cases.iter().any(|c| c.is_empty()) { return; }
        let mut h: u64 = 1469598103934665603;
        h ^= cases.len() as u64; h = h.wrapping_mul(1099511628211);
        for case in &cases {
            h ^= case.len() as u64; h = h.wrapping_mul(1099511628211);
            for &x in case { h ^= x as u64; h = h.wrapping_mul(1099511628211); }
        }
        if !seen.insert(h) { return; }
        let answers: Vec<i32> = cases.iter().map(|c| Solution::count_bad_prices(c.clone())).collect();
        let inp = build_input(&cases);
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    // Big single-case patterns
    for &n in &[1usize, 2, 5, 10, 100, 1000, 10_000, 100_000] {
        emit(vec![vec![1i32; n]], &mut seen, &mut out, &mut count);
        let v: Vec<i32> = (0..n).map(|i| (i + 1) as i32).collect();
        emit(vec![v], &mut seen, &mut out, &mut count);
        let v: Vec<i32> = (0..n).map(|i| (n - i) as i32).collect();
        emit(vec![v], &mut seen, &mut out, &mut count);
        let v: Vec<i32> = (0..n).map(|i| if i % 2 == 0 { 1 } else { 1_000_000 }).collect();
        emit(vec![v], &mut seen, &mut out, &mut count);
    }

    let mut tries = 0;
    while count < target && tries < 5000 {
        tries += 1;
        let t: usize = match tries % 5 {
            0 => 1,
            1 => rng.gen_range_usize(2, 10),
            2 => rng.gen_range_usize(10, 50),
            3 => rng.gen_range_usize(50, 200),
            _ => rng.gen_range_usize(1, 5),
        };
        let mut cases: Vec<Vec<i32>> = Vec::new();
        let mut total_n = 0usize;
        for _ in 0..t {
            if total_n >= 100_000 { break; }
            let max_n = (150_000 - total_n).min(30_000);
            let n = match tries % 6 {
                0 => rng.gen_range_usize(1, 5),
                1 => rng.gen_range_usize(5, 50),
                2 => rng.gen_range_usize(50, 500),
                3 => rng.gen_range_usize(500, 5_000),
                4 => rng.gen_range_usize(5_000, max_n.max(5_000)),
                _ => rng.gen_range_usize(1, 100),
            };
            total_n += n;
            let max_val = match tries % 4 {
                0 => 10i32,
                1 => 1000,
                2 => 100_000,
                _ => 1_000_000,
            };
            cases.push(random_array(&mut rng, n, max_val));
        }
        if !cases.is_empty() {
            emit(cases, &mut seen, &mut out, &mut count);
        }
    }
}

