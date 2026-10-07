use vstd::prelude::*;

verus! {

fn valid_permutation(raw: &Vec<i64>) -> (valid: bool)
    ensures valid ==> (
        2 <= raw.len() <= 200000
        && (forall|i: int| 0 <= i < raw.len() ==> 1 <= #[trigger] raw[i] <= raw.len())
        && (forall|i: int, j: int| 0 <= i < j < raw.len() ==> raw[i] != raw[j])),
{
    if raw.len() < 2 || raw.len() > 200000 { return false; }
    let n = raw.len();
    let mut seen: Vec<bool> = Vec::new();
    let mut i = 0usize;
    while i <= n
        invariant i <= n + 1, 2 <= n <= 200000, seen.len() == i,
            forall|j: int| 0 <= j < i ==> !#[trigger] seen[j],
        decreases n + 1 - i,
    { seen.push(false); i += 1; }
    let mut i = 0usize;
    while i < n
        invariant i <= n, n == raw.len(), 2 <= n <= 200000, seen.len() == n + 1,
            forall|j: int| 0 <= j < i ==> 1 <= #[trigger] raw[j] <= n,
            forall|j: int| 0 <= j < i ==> #[trigger] seen[raw[j] as int],
            forall|j: int, k: int| 0 <= j < k < i ==> raw[j] != raw[k],
        decreases n - i,
    {
        let v = raw[i];
        if v < 1 || v > n as i64 { return false; }
        if seen[v as usize] { return false; }
        assert forall|j: int| 0 <= j < i implies #[trigger] raw[j] != v by {
            assert(seen[raw[j] as int]);
        }
        seen.set(v as usize, true);
        i += 1;
    }
    true
}
fn construct_permutation(raw: Vec<i64>) -> (result: Vec<i64>)
    ensures 2 <= result.len() <= 200000,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= result.len(),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
{
    if valid_permutation(&raw) { return raw; }
    let n = if raw.len() < 2 { 2usize } else if raw.len() > 200000 { 200000usize } else { raw.len() };
    let mut result = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant i <= n, 2 <= n <= 200000, result.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result[j] == j + 1,
        decreases n - i,
    { result.push((i + 1) as i64); i += 1; }
    let mut i = 0usize;
    while i < n
        invariant i <= n, 2 <= n <= 200000, result.len() == n,
            forall|j: int| 0 <= j < n ==> 1 <= #[trigger] result[j] <= n,
            forall|j: int, k: int| 0 <= j < k < n ==> result[j] != result[k],
        decreases n - i,
    {
        let v = if i < raw.len() { raw[i] } else { 1 };
        let j = if v < 1 || v > n as i64 { i } else { (v - 1) as usize };
        let a = result[i]; let b = result[j];
        result.set(i, b); result.set(j, a);
        i += 1;
    }
    result
}
pub fn generate_test_case(a: Vec<i64>, raw_b: Vec<i64>) -> (result: (usize, Vec<i64>, usize, Vec<i64>))
    ensures 2 <= result.0 <= 200000, 1 <= result.2 <= 200000,
        result.1.len() == result.0, result.3.len() == result.2,
        forall|i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i] <= result.0,
        forall|i: int, j: int| 0 <= i < j < result.1.len() ==> result.1[i] != result.1[j],
        forall|i: int| 0 <= i < result.3.len() ==> 1 <= #[trigger] result.3[i] <= result.0 - 1,
{
    let a = construct_permutation(a);
    let n = a.len();
    let m = if raw_b.len() < 1 { 1usize } else if raw_b.len() > 200000 { 200000usize } else { raw_b.len() };
    let mut b = Vec::new();
    let mut i = 0usize;
    while i < m
        invariant i <= m, 1 <= m <= 200000, 2 <= n <= 200000, b.len() == i,
            forall|j: int| 0 <= j < i ==> 1 <= #[trigger] b[j] <= n - 1,
        decreases m - i,
    {
        let v = if i < raw_b.len() { raw_b[i] } else { 1 };
        let v = if v < 1 { 1 } else if v >= n as i64 { (n - 1) as i64 } else { v };
        b.push(v); i += 1;
    }
    (n, a, m, b)
}


pub fn generate_perm(
    n: usize,
    raw: Vec<usize>,
) -> (result: Vec<i64>)
    requires
        2 <= n <= 200000,
        raw.len() == n,
        forall|i: int| 0 <= i < raw.len() ==> #[trigger] raw[i] < n,
    ensures
        result.len() == n,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= n as i64,
{
    let mut v: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            2 <= n <= 200000,
            v.len() == i,
            raw.len() == n,
            forall|k: int| 0 <= k < raw.len() ==> #[trigger] raw[k] < n,
            forall|k: int| 0 <= k < i ==> 1i64 <= #[trigger] v[k] <= n as i64,
        decreases n - i,
    {
        let r = raw[i];
        let val: i64 = (r as i64) + 1i64;
        v.push(val);
        i = i + 1;
    }
    v
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

fn build_input(n: usize, a: &Vec<i64>, m: usize, b: &Vec<i64>) -> String {
    let mut s = format!("1\n{}\n", n);
    for (i, x) in a.iter().enumerate() {
        if i > 0 { s.push(' '); }
        s.push_str(&x.to_string());
    }
    s.push('\n');
    s.push_str(&m.to_string());
    s.push('\n');
    for (i, x) in b.iter().enumerate() {
        if i > 0 { s.push(' '); }
        s.push_str(&x.to_string());
    }
    s.push('\n');
    s
}

fn build_output(ans: i64) -> String { format!("{}\n", ans) }

fn random_permutation(n: usize, rng: &mut Rng) -> Vec<i64> {
    let mut v: Vec<i64> = (1..=(n as i64)).collect();
    for i in 0..n {
        let j = rng.gen_range_usize(i, n - 1);
        v.swap(i, j);
    }
    v
}

fn random_b(n: usize, m: usize, rng: &mut Rng) -> Vec<i64> {
    (0..m).map(|_| rng.gen_range_usize(1, n - 1) as i64).collect()
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(0x1681AA);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut tries = 0;
    while count < target && tries < target * 50 {
        tries += 1;
        let n = match tries % 5 {
            0 => rng.gen_range_usize(2, 5),
            1 => rng.gen_range_usize(2, 10),
            2 => rng.gen_range_usize(10, 50),
            3 => rng.gen_range_usize(50, 200),
            _ => rng.gen_range_usize(200, 2000),
        };
        let m = match tries % 4 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(2, 20),
            2 => rng.gen_range_usize(20, 200),
            _ => rng.gen_range_usize(200, 2000),
        };
        let perm = random_permutation(n, &mut rng);
        let b = random_b(n, m, &mut rng);
        let (n, perm, m, b) = generate_test_case(perm, b);
        let inp = build_input(n, &perm, m, &b);
        if !seen.insert(inp.clone()) { continue; }
        let ans = Solution::top_card(n, perm.clone(), m, b.clone());
        let outp = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}
