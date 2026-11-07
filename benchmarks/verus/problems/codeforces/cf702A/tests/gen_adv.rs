use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: usize, values: &Vec<i64>) -> (res: (usize, Vec<i64>))
    requires
        1 <= n <= 100_000,
        values.len() == n,
        forall|t: int| 0 <= t < values.len() ==> 1 <= #[trigger] values[t] <= 1_000_000_000,
    ensures
        1 <= res.0 <= 100_000,
        res.0 == n,
        res.1.len() == res.0,
        forall|t: int| 0 <= t < res.1.len() ==> 1 <= #[trigger] res.1[t] <= 1_000_000_000,
{
    let mut a: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            a.len() == i,
            values.len() == n,
            forall|t: int| 0 <= t < values.len() ==> 1 <= #[trigger] values[t] <= 1_000_000_000,
            forall|t: int| 0 <= t < a.len() ==> 1 <= #[trigger] a[t] <= 1_000_000_000,
        decreases n - i,
    {
        a.push(values[i]);
        i = i + 1;
    }
    (n, a)
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

fn build_input(a: &[i64]) -> String {
    let mut s = format!("{}\n", a.len());
    let parts: Vec<String> = a.iter().map(|v| v.to_string()).collect();
    s.push_str(&parts.join(" "));
    s.push('\n');
    s
}

fn build_output(ans: usize) -> String { format!("{}\n", ans) }

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(70201);
    let mut seen: HashSet<String> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |a: Vec<i64>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if a.is_empty() || a.len() > 100_000 { return; }
        for &v in &a { if v < 1 || v > 1_000_000_000 { return; } }
        let key = format!("{:?}", a);
        if !seen.insert(key) { return; }
        let inp = build_input(&a);
        let ans = Solution::max_increasing_subarray_len(a.len(), a.clone());
        let outs = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    // Boundaries
    emit(vec![1], &mut seen, &mut out, &mut count);
    emit(vec![1_000_000_000], &mut seen, &mut out, &mut count);
    emit(vec![1; 100_000], &mut seen, &mut out, &mut count);
    emit(vec![1_000_000_000; 100_000], &mut seen, &mut out, &mut count);
    emit((1..=100_000i64).collect(), &mut seen, &mut out, &mut count);
    emit({ let mut v: Vec<i64> = (1..=100_000).collect(); v.reverse(); v }, &mut seen, &mut out, &mut count);

    // Stair patterns
    for &n in &[10usize, 100, 1000, 10_000, 100_000] {
        for &k in &[2usize, 3, 5, 10, 100] {
            if k > n { continue; }
            let v: Vec<i64> = (0..n).map(|i| ((i % k) as i64) + 1).collect();
            emit(v, &mut seen, &mut out, &mut count);
        }
    }

    while count < target {
        let n = match rng.gen_range_usize(0, 5) {
            0 => 1,
            1 => rng.gen_range_usize(2, 10),
            2 => rng.gen_range_usize(10, 100),
            3 => rng.gen_range_usize(100, 1000),
            _ => rng.gen_range_usize(1000, 100_000),
        };
        let max_v: i64 = match rng.gen_range_usize(0, 4) {
            0 => 2,
            1 => 5,
            2 => 1000,
            _ => 1_000_000_000,
        };
        let a: Vec<i64> = (0..n).map(|_| rng.gen_range_i64(1, max_v)).collect();
        emit(a, &mut seen, &mut out, &mut count);
    }
}

