use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    ls: &Vec<i64>,
    rs: &Vec<i64>,
) -> (res: (Vec<i64>, Vec<i64>))
    requires
        2 <= n <= 300_000,
        ls.len() == n,
        rs.len() == n,
        forall|i: int| 0 <= i < n ==> 0 <= #[trigger] ls[i] && ls[i] <= rs[i] && rs[i] <= 1_000_000_000,
    ensures
        2 <= res.0.len() <= 300_000,
        res.0.len() == res.1.len(),
        forall|i: int| 0 <= i < res.0.len() ==> 0 <= #[trigger] res.0[i] && res.0[i] <= res.1[i] && res.1[i] <= 1_000_000_000,
{
    let mut l_out: Vec<i64> = Vec::new();
    let mut r_out: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            l_out.len() == i,
            r_out.len() == i,
            2 <= n <= 300_000,
            ls.len() == n,
            rs.len() == n,
            forall|k: int| 0 <= k < n ==> 0 <= #[trigger] ls[k] && ls[k] <= rs[k] && rs[k] <= 1_000_000_000,
            forall|k: int| 0 <= k < i ==> 0 <= #[trigger] l_out[k] && l_out[k] <= r_out[k] && r_out[k] <= 1_000_000_000,
            forall|k: int| 0 <= k < i ==> l_out[k] == ls[k] && r_out[k] == rs[k],
        decreases n - i,
    {
        l_out.push(ls[i]);
        r_out.push(rs[i]);
        i = i + 1;
    }
    (l_out, r_out)
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
    let target: usize = 200;
    let mut rng = Rng::new(987654321);
    let mut seen: HashSet<u64> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
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

    for &n in &[2usize, 3, 5, 10, 100, 1000, 10_000, 50_000] {
        let l = vec![5i64; n];
        let r = vec![10i64; n];
        emit(l, r, &mut seen, &mut out, &mut count);
        let mut l2 = Vec::with_capacity(n);
        let mut r2 = Vec::with_capacity(n);
        for i in 0..n {
            l2.push((i as i64) * 100);
            r2.push((i as i64) * 100 + 50);
        }
        emit(l2, r2, &mut seen, &mut out, &mut count);
        let l3 = (0..n).map(|i| i as i64).collect::<Vec<_>>();
        let r3 = (0..n).map(|i| i as i64).collect::<Vec<_>>();
        emit(l3, r3, &mut seen, &mut out, &mut count);
        let l4 = vec![0i64; n];
        let r4 = vec![1_000_000_000i64; n];
        emit(l4, r4, &mut seen, &mut out, &mut count);
        let mut l5 = vec![0i64; n];
        let r5 = vec![1_000_000_000i64; n];
        l5[0] = 999_999_999;
        emit(l5, r5, &mut seen, &mut out, &mut count);
    }

    let mut tries = 0;
    while count < target && tries < 10000 {
        tries += 1;
        let n = match tries % 7 {
            0 => rng.gen_range_usize(2, 5),
            1 => rng.gen_range_usize(5, 50),
            2 => rng.gen_range_usize(50, 500),
            3 => rng.gen_range_usize(500, 5000),
            4 => rng.gen_range_usize(5000, 30_000),
            5 => rng.gen_range_usize(30_000, 80_000),
            _ => rng.gen_range_usize(80_000, 150_000),
        };
        let max_val = match tries % 4 {
            0 => 10i64,
            1 => 1_000,
            2 => 1_000_000,
            _ => 1_000_000_000,
        };
        let (l, r) = random_segments(&mut rng, n, max_val);
        emit(l, r, &mut seen, &mut out, &mut count);
    }
}

