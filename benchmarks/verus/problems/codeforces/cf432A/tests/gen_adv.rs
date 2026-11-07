use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    k: i32,
    y: Vec<i64>,
) -> (result: (usize, i32, Vec<i64>))
    requires
        1 <= n <= 2000,
        n == y.len(),
        1 <= k as int <= 5,
        forall|i: int| 0 <= i < n as int ==> 0 <= (#[trigger] y[i] as int) <= 5,
    ensures
        ({
            let (rn, rk, ry) = result;
            &&& 1 <= rn <= 2000
            &&& rn == ry.len()
            &&& 1 <= rk as int <= 5
            &&& forall|i: int| 0 <= i < rn as int ==> 0 <= (#[trigger] ry[i] as int) <= 5
        }),
{
    (n, k, y)
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

fn build_input(n: usize, k: i32, y: &[i64]) -> String {
    let mut s = format!("{} {}\n", n, k);
    let parts: Vec<String> = y.iter().map(|x| x.to_string()).collect();
    s.push_str(&parts.join(" "));
    s.push('\n');
    s
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(1);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |n: usize, k: i32, y: Vec<i64>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if !(1 <= n && n <= 2000 && 1 <= k && k <= 5 && y.len() == n) { return; }
        for &v in &y { if !(0 <= v && v <= 5) { return; } }
        let key = format!("{} {} {:?}", n, k, y);
        if !seen.insert(key) { return; }
        let inp = build_input(n, k, &y);
        let ans = Solution::max_teams(n, k, y.clone());
        let outs = format!("{}\n", ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    let mut tries = 0usize;
    while count < target {
        tries += 1;
        if tries > 100000 { break; }
        let mode = tries % 8;
        let n = match mode {
            0 => 1,
            1 => 2,
            2 => 3,
            3 => 2000,
            4 => rng.gen_range_usize(3, 9),
            5 => rng.gen_range_usize(100, 500),
            6 => rng.gen_range_usize(1000, 2000),
            _ => rng.gen_range_usize(1, 100),
        };
        let k = rng.gen_range_i64(1, 5) as i32;
        let y: Vec<i64> = match mode % 4 {
            0 => vec![0; n],
            1 => vec![5; n],
            2 => (0..n).map(|i| (i % 6) as i64).collect(),
            _ => (0..n).map(|_| rng.gen_range_i64(0, 5)).collect(),
        };
        emit(n, k, y, &mut seen, &mut out, &mut count);
    }
}

