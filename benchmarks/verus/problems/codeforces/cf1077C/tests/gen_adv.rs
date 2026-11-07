use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: usize, vals: &Vec<i32>) -> (res: (usize, Vec<i32>))
    requires
        2 <= n <= 200_000,
        vals.len() == n,
        forall|i: int| 0 <= i < n ==> 1 <= #[trigger] vals[i] <= 1_000_000,
    ensures
        res.0 == n,
        res.1.len() == n,
        2 <= res.0 <= 200_000,
        forall|i: int| 0 <= i < res.0 as int ==> 1 <= #[trigger] res.1[i] <= 1_000_000,
{
    let mut a: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            a.len() == i,
            vals.len() == n,
            forall|k: int| 0 <= k < n ==> 1 <= #[trigger] vals[k] <= 1_000_000,
            forall|k: int| 0 <= k < i as int ==> 1 <= #[trigger] a[k] <= 1_000_000,
            forall|k: int| 0 <= k < i as int ==> a[k] == vals[k],
        decreases n - i,
    {
        a.push(vals[i]);
        i += 1;
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

fn build_input(a: &[i32]) -> String {
    let mut s = format!("{}\n", a.len());
    let parts: Vec<String> = a.iter().map(|x| x.to_string()).collect();
    s.push_str(&parts.join(" "));
    s.push('\n');
    s
}

fn build_output(res: &[i32]) -> String {
    let mut s = format!("{}\n", res.len());
    if !res.is_empty() {
        let parts: Vec<String> = res.iter().map(|x| x.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
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

    let mut emit = |a: Vec<i32>, seen: &mut HashSet<u64>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        let mut h: u64 = 1469598103934665603;
        h ^= a.len() as u64;
        h = h.wrapping_mul(1099511628211);
        for &x in &a { h ^= x as u64; h = h.wrapping_mul(1099511628211); }
        if !seen.insert(h) { return; }
        let inp = build_input(&a);
        let res = Solution::nice_indices(a.len(), a.clone());
        let outs = build_output(&res);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    // Patterns
    for &n in &[2usize, 5, 10, 100, 1000, 10_000, 50_000] {
        emit(vec![1i32; n], &mut seen, &mut out, &mut count);
        emit(vec![1_000_000i32; n], &mut seen, &mut out, &mut count);
        let v: Vec<i32> = (0..n).map(|i| ((i + 1) as i32 % 1000) + 1).collect();
        emit(v, &mut seen, &mut out, &mut count);
    }

    let mut tries = 0;
    while count < target && tries < 5000 {
        tries += 1;
        let n = match tries % 6 {
            0 => rng.gen_range_usize(2, 5),
            1 => rng.gen_range_usize(5, 50),
            2 => rng.gen_range_usize(50, 500),
            3 => rng.gen_range_usize(500, 5_000),
            4 => rng.gen_range_usize(5_000, 30_000),
            _ => rng.gen_range_usize(30_000, 100_000),
        };
        let max_val = match tries % 4 {
            0 => 10i32,
            1 => 100,
            2 => 10_000,
            _ => 1_000_000,
        };
        let v = random_array(&mut rng, n, max_val);
        emit(v, &mut seen, &mut out, &mut count);
    }
}

