use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    fillers: &Vec<i64>,
) -> (loads: Vec<i64>)
    requires
        1 <= fillers.len() <= 100000,
        forall |j: int| #![trigger fillers@[j]] 0 <= j < fillers.len() ==> 0 <= (fillers@[j] as int) <= 20000,
    ensures
        1 <= loads.len() <= 100000,
        forall |j: int| #![trigger loads@[j]] 0 <= j < loads.len() ==> 0 <= (loads@[j] as int) <= 20000,
{
    let mut loads: Vec<i64> = Vec::new();
    let n = fillers.len();
    let mut i: usize = 0;
    while i < n
        invariant
            n == fillers.len(),
            0 <= i <= n,
            loads.len() == i,
            forall |j: int| #![trigger fillers@[j]] 0 <= j < fillers.len() ==> 0 <= (fillers@[j] as int) <= 20000,
            forall |j: int| #![trigger loads@[j]] 0 <= j < i as int ==> loads@[j] == fillers@[j],
        decreases n - i,
    {
        loads.push(fillers[i]);
        i = i + 1;
    }
    loads
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

fn build_input(loads: &[i64]) -> String {
    let mut s = format!("{}\n", loads.len());
    let parts: Vec<String> = loads.iter().map(|v| v.to_string()).collect();
    s.push_str(&parts.join(" "));
    s.push('\n');
    s
}

fn build_output(ans: i64) -> String { format!("{}\n", ans) }

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(60901);
    let mut seen: HashSet<String> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |a: Vec<i64>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if a.is_empty() || a.len() > 100_000 { return; }
        for &v in &a { if v < 0 || v > 20_000 { return; } }
        let key = format!("{:?}", a);
        if !seen.insert(key) { return; }
        let inp = build_input(&a);
        let ans = Solution::min_balance_seconds(&a);
        let outs = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    // Boundary
    emit(vec![0], &mut seen, &mut out, &mut count);
    emit(vec![20_000], &mut seen, &mut out, &mut count);
    emit(vec![0; 100_000], &mut seen, &mut out, &mut count);
    emit(vec![20_000; 100_000], &mut seen, &mut out, &mut count);
    emit(vec![10_000; 100_000], &mut seen, &mut out, &mut count);

    // Half/half
    let mut hh: Vec<i64> = vec![0; 50_000]; hh.extend(vec![20_000; 50_000].iter()); emit(hh, &mut seen, &mut out, &mut count);
    let mut hh2: Vec<i64> = vec![0; 1]; hh2.extend(vec![20_000; 99_999].iter()); emit(hh2, &mut seen, &mut out, &mut count);

    // Various sizes
    for &n in &[1usize, 2, 10, 100, 1000, 10_000, 50_000, 100_000] {
        emit(vec![0; n], &mut seen, &mut out, &mut count);
        emit(vec![1; n], &mut seen, &mut out, &mut count);
        emit(vec![20_000; n], &mut seen, &mut out, &mut count);
        let mixed: Vec<i64> = (0..n as i64).map(|i| i % 20_001).collect();
        emit(mixed, &mut seen, &mut out, &mut count);
    }

    while count < target {
        let n = match rng.gen_range_usize(0, 5) {
            0 => 1,
            1 => rng.gen_range_usize(2, 100),
            2 => rng.gen_range_usize(100, 1000),
            3 => rng.gen_range_usize(1000, 10_000),
            _ => rng.gen_range_usize(10_000, 100_000),
        };
        let max_v: i64 = match rng.gen_range_usize(0, 4) {
            0 => 5,
            1 => 100,
            2 => 1000,
            _ => 20_000,
        };
        let a: Vec<i64> = (0..n).map(|_| rng.gen_range_i64(0, max_v)).collect();
        emit(a, &mut seen, &mut out, &mut count);
    }
}

