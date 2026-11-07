use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    lefts: &Vec<i32>,
    rights: &Vec<i32>,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        1 <= n <= 100_000,
        lefts.len() == n,
        rights.len() == n,
        forall|i: int| 0 <= i < n as int ==> 1 <= #[trigger] lefts[i] <= rights[i] <= 1_000_000_000,
        forall|i: int, j: int|
            0 <= i < j < n as int ==> lefts[i] != lefts[j] || rights[i] != rights[j],
    ensures
        result.0.len() == result.1.len(),
        1 <= result.0.len() <= 100_000,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= result.1[i] <= 1_000_000_000,
        forall|i: int, j: int|
            0 <= i < j < result.0.len() as int ==> result.0[i] != result.0[j] || result.1[i] != result.1[j],
{
    let mut l_out: Vec<i32> = Vec::new();
    let mut r_out: Vec<i32> = Vec::new();
    let mut k: usize = 0;
    while k < n
        invariant
            k <= n,
            1 <= n <= 100_000,
            lefts.len() == n,
            rights.len() == n,
            l_out.len() == k,
            r_out.len() == k,
            forall|i: int| 0 <= i < k as int ==> l_out[i] == lefts[i] && r_out[i] == rights[i],
            forall|i: int| 0 <= i < n as int ==> 1 <= #[trigger] lefts[i] <= rights[i] <= 1_000_000_000,
            forall|i: int, j: int|
                0 <= i < j < n as int ==> lefts[i] != lefts[j] || rights[i] != rights[j],
        decreases n - k,
    {
        l_out.push(lefts[k]);
        r_out.push(rights[k]);
        k = k + 1;
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

fn build_input(left: &[i32], right: &[i32]) -> String {
    let n = left.len();
    let mut s = format!("{}\n", n);
    for i in 0..n {
        s.push_str(&format!("{} {}\n", left[i], right[i]));
    }
    s
}

fn build_output(ans: i32) -> String {
    if ans == 0 { "-1\n".to_string() } else { format!("{}\n", ans) }
}

fn random_unique_segments(rng: &mut Rng, n: usize, max: i64) -> (Vec<i32>, Vec<i32>) {
    let mut seen = HashSet::new();
    let mut left = Vec::with_capacity(n);
    let mut right = Vec::with_capacity(n);
    let mut tries = 0;
    while left.len() < n && tries < n * 100 {
        tries += 1;
        let l = rng.gen_range_i64(1, max) as i32;
        let r = rng.gen_range_i64(l as i64, max) as i32;
        if seen.insert((l, r)) {
            left.push(l);
            right.push(r);
        }
    }
    (left, right)
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(0x242BB);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut tries = 0;
    while count < target && tries < target * 100 {
        tries += 1;
        let n = match tries % 6 {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(3, 30),
            2 => rng.gen_range_usize(30, 200),
            3 => rng.gen_range_usize(200, 1000),
            4 => rng.gen_range_usize(1000, 10000),
            _ => rng.gen_range_usize(10000, 100000),
        };
        let max_val = match tries % 3 {
            0 => 1_000_000_000i64,
            1 => 100i64,
            _ => 10_000i64,
        };
        let (l, r) = random_unique_segments(&mut rng, n, max_val);
        if l.is_empty() { continue; }
        let inp = build_input(&l, &r);
        if !seen.insert(inp.clone()) { continue; }
        let ans = Solution::find_covering_segment(l, r);
        let outp = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

