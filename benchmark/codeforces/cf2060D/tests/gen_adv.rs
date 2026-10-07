use vstd::prelude::*;

verus! {

pub fn generate_test_case(fillers: &Vec<i64>) -> (a: Vec<i64>)
    requires
        2 <= fillers.len() <= 200_000,
        forall |k: int| 0 <= k < fillers.len() ==> 1 <= #[trigger] fillers[k] <= 1_000_000_000,
    ensures
        2 <= a.len() <= 200_000,
        a.len() == fillers.len(),
        forall |k: int| 0 <= k < a.len() ==> 1 <= #[trigger] a[k] <= 1_000_000_000,
{
    let n = fillers.len();
    let mut a: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == fillers.len(),
            2 <= n <= 200_000,
            0 <= i <= n,
            a.len() == i,
            forall |k: int| 0 <= k < fillers.len() ==> 1 <= #[trigger] fillers[k] <= 1_000_000_000,
            forall |k: int| 0 <= k < i as int ==> #[trigger] a[k] == fillers[k],
        decreases n - i,
    {
        a.push(fillers[i]);
        i = i + 1;
    }
    a
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

fn build_input_multi(cases: &[Vec<i64>]) -> String {
    let mut s = format!("{}\n", cases.len());
    for a in cases {
        s.push_str(&format!("{}\n", a.len()));
        let parts: Vec<String> = a.iter().map(|x| x.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn build_output_multi(answers: &[bool]) -> String {
    let mut s = String::new();
    for &a in answers {
        s.push_str(if a { "YES\n" } else { "NO\n" });
    }
    s
}

fn build_seed(rng: &mut Rng, mode: usize) -> Vec<i64> {
    match mode {
        0 => {
            // Already sorted with rare equal
            let n = rng.gen_range_usize(2, 200);
            let mut v = Vec::with_capacity(n);
            let mut cur: i64 = rng.gen_range_i64(1, 100);
            for _ in 0..n {
                v.push(cur);
                cur += rng.gen_range_i64(0, 100);
                if cur > 1_000_000_000 { cur = 1_000_000_000; }
            }
            v
        }
        1 => {
            // Strictly decreasing tail
            let n = rng.gen_range_usize(3, 100);
            let mut v = Vec::with_capacity(n);
            let mut cur: i64 = rng.gen_range_i64(n as i64 + 100, 1_000_000_000);
            for _ in 0..n {
                v.push(cur);
                cur -= rng.gen_range_i64(1, 100);
                if cur < 1 { cur = 1; }
            }
            v
        }
        2 => {
            // All equal
            let n = rng.gen_range_usize(2, 1000);
            let x = rng.gen_range_i64(1, 1_000_000_000);
            vec![x; n]
        }
        3 => {
            // n=2 random
            vec![rng.gen_range_i64(1, 1_000_000_000), rng.gen_range_i64(1, 1_000_000_000)]
        }
        4 => {
            // Random close to max
            let n = rng.gen_range_usize(2, 200);
            (0..n).map(|_| rng.gen_range_i64(999_000_000, 1_000_000_000)).collect()
        }
        5 => {
            // All 1s
            let n = rng.gen_range_usize(2, 1000);
            vec![1i64; n]
        }
        6 => {
            // Mostly small with random
            let n = rng.gen_range_usize(2, 500);
            (0..n).map(|_| rng.gen_range_i64(1, 100)).collect()
        }
        7 => {
            // Random large
            let n = rng.gen_range_usize(2, 500);
            (0..n).map(|_| rng.gen_range_i64(1, 1_000_000_000)).collect()
        }
        8 => {
            // Zigzag
            let n = rng.gen_range_usize(4, 200);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                if i % 2 == 0 {
                    v.push(rng.gen_range_i64(1, 10000));
                } else {
                    v.push(rng.gen_range_i64(500_000_000, 1_000_000_000));
                }
            }
            v
        }
        9 => {
            // Big spike at start
            let n = rng.gen_range_usize(2, 100);
            let mut v = Vec::with_capacity(n);
            v.push(rng.gen_range_i64(500_000_000, 1_000_000_000));
            for _ in 1..n {
                v.push(rng.gen_range_i64(1, 100));
            }
            v
        }
        10 => {
            // [a, a, b, b, ...] cancellation pattern
            let n = rng.gen_range_usize(3, 200);
            let mut v = Vec::with_capacity(n);
            let a = rng.gen_range_i64(50, 1_000_000);
            let b = rng.gen_range_i64(1, a - 1);
            v.push(a);
            v.push(a);
            for _ in 2..n {
                v.push(b);
            }
            v
        }
        _ => {
            // Stress
            let n = if mode % 2 == 0 { 5000 } else { 1000 };
            (0..n).map(|i| (((i as i64) % 1000) + 1).min(1_000_000_000)).collect()
        }
    }
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(0xCFCFCF);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    while count < target {
        let t: usize = if count < 50 {
            rng.gen_range_usize(1, 5)
        } else if count < 150 {
            rng.gen_range_usize(2, 20)
        } else {
            rng.gen_range_usize(20, 50)
        };
        let mut cases: Vec<Vec<i64>> = Vec::with_capacity(t);
        let mut total_n = 0usize;
        for _ in 0..t {
            let mode = rng.gen_range_usize(0, 11);
            let seed_v = build_seed(&mut rng, mode);
            // Filter to satisfy preconditions: 2 <= len <= 200_000
            if seed_v.len() < 2 || seed_v.len() > 200_000 { continue; }
            // Ensure all elements are in [1, 1_000_000_000]
            let mut ok = true;
            for &x in &seed_v {
                if x < 1 || x > 1_000_000_000 { ok = false; break; }
            }
            if !ok { continue; }
            if total_n + seed_v.len() > 200_000 { break; }
            total_n += seed_v.len();
            let v = generate_test_case(&seed_v);
            cases.push(v);
        }
        if cases.is_empty() { continue; }
        let answers: Vec<bool> = cases.iter().map(|a| Solution::can_sort(a.clone())).collect();
        let inp = build_input_multi(&cases);
        let outp = build_output_multi(&answers);
        if !seen.insert(inp.clone()) { continue; }
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}
