use vstd::prelude::*;

verus! {

pub open spec fn sum_seq(s: Seq<i64>) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        0int
    } else {
        s[0] as int + sum_seq(s.skip(1))
    }
}

pub fn generate_test_case(
    a: Vec<i64>,
    b: Vec<i64>,
) -> (result: (Vec<i64>, Vec<i64>))
    requires
        1 <= a.len() <= 300_000,
        1 <= b.len() <= 300_000,
        forall|x: int| 0 <= x < a.len() ==> 1 <= #[trigger] a[x] as int && (a[x] as int) <= 1_000_000_000,
        forall|x: int| 0 <= x < b.len() ==> 1 <= #[trigger] b[x] as int && (b[x] as int) <= 1_000_000_000,
    ensures
        1 <= result.0.len() <= 300_000,
        1 <= result.1.len() <= 300_000,
        forall|x: int| 0 <= x < result.0.len() ==> 1 <= #[trigger] result.0[x] as int && (result.0[x] as int) <= 1_000_000_000,
        forall|x: int| 0 <= x < result.1.len() ==> 1 <= #[trigger] result.1[x] as int && (result.1[x] as int) <= 1_000_000_000,
{
    (a, b)
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

fn build_input(a: &[i64], b: &[i64]) -> String {
    let mut s = format!("{}\n", a.len());
    let pa: Vec<String> = a.iter().map(|x| x.to_string()).collect();
    s.push_str(&pa.join(" "));
    s.push('\n');
    s.push_str(&format!("{}\n", b.len()));
    let pb: Vec<String> = b.iter().map(|x| x.to_string()).collect();
    s.push_str(&pb.join(" "));
    s.push('\n');
    s
}

fn build_output(ans: i64) -> String { format!("{}\n", ans) }

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

    let mut emit = |a: Vec<i64>, b: Vec<i64>, seen: &mut HashSet<u64>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        let mut h: u64 = 1469598103934665603;
        h ^= a.len() as u64;
        h = h.wrapping_mul(1099511628211);
        for &x in &a { h ^= x as u64; h = h.wrapping_mul(1099511628211); }
        h ^= b.len() as u64;
        for &x in &b { h ^= x as u64; h = h.wrapping_mul(1099511628211); }
        if !seen.insert(h) { return; }
        let inp = build_input(&a, &b);
        let ans = Solution::max_equal_block_count(a, b);
        let outs = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    // Same arrays of various sizes
    for &n in &[1usize, 2, 5, 10, 100, 1000, 10_000, 50_000] {
        emit(vec![1i64; n], vec![1i64; n], &mut seen, &mut out, &mut count);
        emit(vec![1_000_000_000i64; n], vec![1_000_000_000i64; n], &mut seen, &mut out, &mut count);
    }

    // a: many small, b: one big totaling same
    for &n in &[2usize, 5, 10, 100, 1000] {
        let a = vec![1i64; n];
        let b = vec![n as i64];
        emit(a, b, &mut seen, &mut out, &mut count);
    }

    // Mismatched totals (return -1)
    for &n in &[2usize, 5, 10, 100, 1000] {
        let a = vec![1i64; n];
        let b = vec![2i64; n];
        emit(a, b, &mut seen, &mut out, &mut count);
    }

    let mut tries = 0;
    while count < target && tries < 10000 {
        tries += 1;
        let n = match tries % 7 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(5, 50),
            2 => rng.gen_range_usize(50, 500),
            3 => rng.gen_range_usize(500, 5_000),
            4 => rng.gen_range_usize(5_000, 30_000),
            5 => rng.gen_range_usize(30_000, 80_000),
            _ => rng.gen_range_usize(80_000, 150_000),
        };
        let m = match tries % 3 {
            0 => n,
            1 => rng.gen_range_usize(1, n.max(2)),
            _ => rng.gen_range_usize(1, (n*2).max(2).min(150_000)),
        };
        let max_val = match tries % 4 {
            0 => 10i64,
            1 => 1_000,
            2 => 1_000_000,
            _ => 1_000_000_000,
        };
        let a = random_array(&mut rng, n, max_val);
        let b = random_array(&mut rng, m, max_val);
        emit(a, b, &mut seen, &mut out, &mut count);
    }
}

