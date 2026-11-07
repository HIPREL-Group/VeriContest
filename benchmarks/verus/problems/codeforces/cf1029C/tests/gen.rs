use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    a_vals: Vec<i64>,
    b_vals: Vec<i64>,
    mutation_kind: u8,
) -> (result: (Vec<i64>, Vec<i64>))
    requires
        2 <= a_vals.len() <= 300_000,
        a_vals.len() == b_vals.len(),
        forall|i: int| 0 <= i < a_vals.len() ==> 0 <= #[trigger] a_vals[i] <= 1_000_000_000,
        forall|i: int| 0 <= i < b_vals.len() ==> 0 <= #[trigger] b_vals[i] <= 1_000_000_000,
    ensures
        2 <= result.0.len() <= 300_000,
        result.0.len() == result.1.len(),
        forall|i: int|
            0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] && result.0[i] <= result.1[i] && result.1[i] <= 1_000_000_000,
{
    let n = a_vals.len();
    let mut l: Vec<i64> = Vec::new();
    let mut r: Vec<i64> = Vec::new();
    let mut idx: usize = 0;

    while idx < n
        invariant
            n == a_vals.len(),
            n == b_vals.len(),
            2 <= n <= 300_000,
            l.len() == idx,
            r.len() == idx,
            idx <= n,
            forall|i: int| 0 <= i < a_vals.len() ==> 0 <= #[trigger] a_vals[i] <= 1_000_000_000,
            forall|i: int| 0 <= i < b_vals.len() ==> 0 <= #[trigger] b_vals[i] <= 1_000_000_000,
            forall|j: int| 0 <= j < idx as int ==> (
                0 <= #[trigger] l[j] && l[j] <= r[j] && r[j] <= 1_000_000_000
            ),
        decreases n - idx,
    {
        let a = a_vals[idx];
        let b = b_vals[idx];

        if mutation_kind == 1 {
            // Degenerate segments: l[i] = r[i]
            l.push(a);
            r.push(a);
        } else if mutation_kind == 2 {
            // All segments start at 0
            let mx = if a > b { a } else { b };
            l.push(0i64);
            r.push(mx);
        } else if mutation_kind == 3 {
            // Full range [0, 1_000_000_000]
            l.push(0i64);
            r.push(1_000_000_000i64);
        } else {
            // Default: sort pair so l <= r
            let lo = if a <= b { a } else { b };
            let hi = if a >= b { a } else { b };
            l.push(lo);
            r.push(hi);
        }

        idx = idx + 1;
    }

    (l, r)
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

fn build_input(l: &[i64], r: &[i64]) -> String {
    let n = l.len();
    let mut s = format!("{}\n", n);
    for i in 0..n {
        s.push_str(&format!("{} {}\n", l[i], r[i]));
    }
    s
}

fn build_output(ans: i64) -> String { format!("{}\n", ans) }

fn random_segments(rng: &mut Rng, n: usize, max_val: i64) -> (Vec<i64>, Vec<i64>) {
    let mut l = Vec::with_capacity(n);
    let mut r = Vec::with_capacity(n);
    for _ in 0..n {
        let a = rng.gen_range_i64(0, max_val);
        let b = rng.gen_range_i64(a, max_val);
        l.push(a);
        r.push(b);
    }
    (l, r)
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let mut seen: HashSet<u64> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |l: Vec<i64>, r: Vec<i64>, seen: &mut HashSet<u64>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        let mut h: u64 = 1469598103934665603;
        h ^= l.len() as u64;
        h = h.wrapping_mul(1099511628211);
        for &x in &l { h ^= x as u64; h = h.wrapping_mul(1099511628211); }
        for &x in &r { h ^= x as u64; h = h.wrapping_mul(1099511628211); }
        if !seen.insert(h) { return; }
        let inp = build_input(&l, &r);
        let ans = Solution::maximal_intersection_len(l, r);
        let outs = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    emit(vec![1,2,0,3], vec![3,6,4,3], &mut seen, &mut out, &mut count);
    emit(vec![2,1,0,1,0], vec![6,3,4,20,4], &mut seen, &mut out, &mut count);
    emit(vec![4,1,9], vec![5,2,20], &mut seen, &mut out, &mut count);
    emit(vec![3,1], vec![10,5], &mut seen, &mut out, &mut count);

    emit(vec![0,0], vec![0,0], &mut seen, &mut out, &mut count);
    emit(vec![0,1_000_000_000], vec![1_000_000_000,1_000_000_000], &mut seen, &mut out, &mut count);
    emit(vec![5,5], vec![5,5], &mut seen, &mut out, &mut count);
    emit(vec![0,0], vec![1_000_000_000,0], &mut seen, &mut out, &mut count);
    emit(vec![10,20], vec![30,40], &mut seen, &mut out, &mut count);

    while count < target {
        let n = match count % 5 {
            0 => rng.gen_range_usize(2, 5),
            1 => rng.gen_range_usize(2, 10),
            2 => rng.gen_range_usize(10, 50),
            3 => rng.gen_range_usize(20, 200),
            _ => rng.gen_range_usize(100, 1000),
        };
        let max_val = match count % 4 {
            0 => 10i64,
            1 => 100,
            2 => 10_000,
            _ => 1_000_000_000,
        };
        let (l, r) = random_segments(&mut rng, n, max_val);
        emit(l, r, &mut seen, &mut out, &mut count);
    }
}

