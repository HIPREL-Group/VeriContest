use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    values: &Vec<i64>,
) -> (a: Vec<i64>)
    requires
        1 <= values.len() <= 100_000,
        forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 1_000_000_000,
    ensures
        1 <= a.len() <= 100_000,
        a.len() == values.len(),
        forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= 1_000_000_000,
{
    let n = values.len();
    let mut a: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == values.len(),
            a.len() == i,
            forall|k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 1_000_000_000,
            forall|k: int| 0 <= k < i as int ==> #[trigger] a[k] == values[k],
            forall|k: int| 0 <= k < i as int ==> 1 <= #[trigger] a[k] <= 1_000_000_000,
        decreases n - i,
    {
        a.push(values[i]);
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
    let mut rng = Rng::new(58001);
    let mut seen: HashSet<String> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |a: Vec<i64>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| -> bool {
        if *count >= target { return false; }
        if a.is_empty() || a.len() > 100_000 { return false; }
        for &v in &a { if v < 1 || v > 1_000_000_000 { return false; } }
        let key = format!("{:?}", a);
        if !seen.insert(key) { return false; }
        let inp = build_input(&a);
        let ans = Solution::longest_non_decreasing_run(a.clone());
        let outs = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
        true
    };

    // Boundary
    emit(vec![1], &mut seen, &mut out, &mut count);
    emit(vec![1_000_000_000], &mut seen, &mut out, &mut count);
    emit(vec![1, 1_000_000_000], &mut seen, &mut out, &mut count);
    emit(vec![1_000_000_000, 1], &mut seen, &mut out, &mut count);
    emit(vec![1; 100_000], &mut seen, &mut out, &mut count);
    emit((1..=100_000i64).collect(), &mut seen, &mut out, &mut count);
    emit({
        let mut v: Vec<i64> = (1..=100_000i64).collect();
        v.reverse();
        v
    }, &mut seen, &mut out, &mut count);
    emit(vec![1_000_000_000; 100_000], &mut seen, &mut out, &mut count);

    // Stair patterns
    for &n in &[10usize, 100, 1000, 10_000, 100_000] {
        let v: Vec<i64> = (0..n).map(|i| ((i / 5) as i64) + 1).collect();
        emit(v, &mut seen, &mut out, &mut count);
        // alternating up/down
        let v2: Vec<i64> = (0..n).map(|i| if i % 2 == 0 { 1 } else { 2 }).collect();
        emit(v2, &mut seen, &mut out, &mut count);
        // single jump down
        let mut v3: Vec<i64> = (1..=n as i64).collect();
        if n >= 2 { v3[n / 2] = 1; }
        emit(v3, &mut seen, &mut out, &mut count);
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

