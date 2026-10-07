use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    start: i64,
    gaps: &Vec<i64>,
) -> (result: (usize, Vec<i64>))
    requires
        gaps.len() >= 1,
        gaps.len() <= 199_999,
        forall|i: int| 0 <= i < gaps.len() ==> 1 <= #[trigger] gaps[i] <= 1000,
        -1_000_000_000 <= start <= -500_000_000,
    ensures
        2 <= result.0 <= 200_000,
        result.0 == result.1.len(),
        result.0 == gaps.len() + 1,
        forall|u: int|
            0 <= u < result.1.len() as int - 1 ==> #[trigger] result.1[u] < result.1[u + 1],
        forall|u: int|
            0 <= u < result.1.len() ==> -1_000_000_000 <= #[trigger] result.1[u] <= 1_000_000_000,
{
    let n: usize = gaps.len() + 1;
    let mut a: Vec<i64> = Vec::new();
    a.push(start);

    let mut i: usize = 0;
    while i < gaps.len()
        invariant
            0 <= i <= gaps.len(),
            a.len() == i + 1,
            a[0] == start,
            gaps.len() >= 1,
            gaps.len() <= 199_999,
            forall|k: int| 0 <= k < gaps.len() ==> 1 <= #[trigger] gaps[k] <= 1000,
            -1_000_000_000 <= start <= -500_000_000,
            forall|u: int| 0 <= u < a.len() as int - 1 ==> #[trigger] a[u] < a[u + 1],
            forall|u: int| 0 <= u < a.len() ==> -1_000_000_000 <= #[trigger] a[u] <= 1_000_000_000,
            a[i as int] <= start + (i as int) * 1000,
            a[i as int] >= start,
        decreases gaps.len() - i,
    {
        let prev: i64 = a[i];
        let g: i64 = gaps[i];
        let next: i64 = prev + g;
        assert(prev <= start + (i as int) * 1000);
        assert(start + (i as int) * 1000 <= -500_000_000 + 199_999 * 1000);
        assert(next <= prev + 1000);
        a.push(next);
        i = i + 1;
        assert(a[i as int] == next);
        assert(a[i as int] <= start + (i as int) * 1000);
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

fn build_output(x: i64, y: i64) -> String { format!("{} {}\n", x, y) }

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(79201);
    let mut seen: HashSet<String> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |a: Vec<i64>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if a.len() < 2 || a.len() > 200_000 { return; }
        for &v in &a { if v < -1_000_000_000 || v > 1_000_000_000 { return; } }
        let mut sorted = a.clone(); sorted.sort_unstable();
        for w in sorted.windows(2) { if w[0] == w[1] { return; } }
        let key = format!("{:?}", a);
        if !seen.insert(key) { return; }
        let inp = build_input(&a);
        let mut sa = a.clone(); sa.sort_unstable();
        let (x, y) = Solution::min_gap_and_count(sa.len(), sa);
        let outs = build_output(x, y);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    // Boundary cases
    emit(vec![-1_000_000_000, 1_000_000_000], &mut seen, &mut out, &mut count);
    emit(vec![-1_000_000_000, -999_999_999], &mut seen, &mut out, &mut count);
    emit(vec![999_999_999, 1_000_000_000], &mut seen, &mut out, &mut count);
    // Large arithmetic progression
    let prog: Vec<i64> = (0..200_000i64).collect();
    emit(prog.clone(), &mut seen, &mut out, &mut count);
    // Reversed
    let mut rev = prog.clone(); rev.reverse(); emit(rev, &mut seen, &mut out, &mut count);
    // Larger gaps
    let prog2: Vec<i64> = (0..100_000i64).map(|i| i * 10).collect();
    emit(prog2, &mut seen, &mut out, &mut count);
    // Two close, rest far
    let mut close: Vec<i64> = vec![0, 1];
    for i in 0..100 { close.push(1000 + i * 1000); }
    emit(close, &mut seen, &mut out, &mut count);

    while count < target {
        let n = match rng.gen_range_usize(0, 5) {
            0 => 2,
            1 => rng.gen_range_usize(2, 10),
            2 => rng.gen_range_usize(10, 100),
            3 => rng.gen_range_usize(100, 10_000),
            _ => rng.gen_range_usize(10_000, 200_000),
        };
        let max_v: i64 = match rng.gen_range_usize(0, 4) {
            0 => (n as i64) * 2 + 100,
            1 => 1000,
            2 => 1_000_000,
            _ => 1_000_000_000,
        };
        if max_v < n as i64 { continue; }
        let mut s: HashSet<i64> = HashSet::new();
        let mut a: Vec<i64> = Vec::with_capacity(n);
        let mut tries = 0;
        while a.len() < n && tries < n * 10 {
            tries += 1;
            let v = rng.gen_range_i64(-max_v, max_v);
            if s.insert(v) { a.push(v); }
        }
        if a.len() != n { continue; }
        emit(a, &mut seen, &mut out, &mut count);
    }
}

