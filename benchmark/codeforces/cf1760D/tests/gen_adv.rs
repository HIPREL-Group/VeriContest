use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    a: Vec<i64>,
) -> (result: (usize, Vec<i64>))
    requires
        1 <= n <= 200000,
        a.len() == n,
        forall|i: int| 0 <= i && i < n ==> 1 <= #[trigger] a[i] <= 1000000000,
    ensures
        ({
            let (rn, ra) = result;
            &&& 1 <= rn <= 200000
            &&& ra.len() == rn
            &&& forall|i: int| 0 <= i && i < rn as int ==> 1 <= #[trigger] ra[i] <= 1000000000
        }),
{
    (n, a)
}

}

use std::io::Write;
use std::collections::HashSet;

struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self { Self(seed.wrapping_add(1)) }
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

type TC = Vec<i64>;

fn build_input(cases: &[TC]) -> String {
    let mut s = format!("{}\n", cases.len());
    for a in cases {
        s.push_str(&format!("{}\n", a.len()));
        let parts: Vec<String> = a.iter().map(|x| x.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn build_output(cases: &[TC]) -> String {
    let mut s = String::new();
    for a in cases {
        let n = a.len();
        let count = Solution::is_valley(n, a.clone());
        s.push_str(if count == 1 { "YES\n" } else { "NO\n" });
    }
    s
}

fn gen_case(rng: &mut Rng, mode: usize) -> TC {
    match mode {
        0 => {
            // n=1
            vec![rng.gen_range_i64(1, 1_000_000_000)]
        }
        1 => {
            // all same
            let n = rng.gen_range_usize(2, 100);
            vec![rng.gen_range_i64(1, 1_000_000_000); n]
        }
        2 => {
            // sorted ascending
            let n = rng.gen_range_usize(2, 100);
            let mut v: Vec<i64> = (0..n).map(|_| rng.gen_range_i64(1, 1000)).collect();
            v.sort();
            v
        }
        3 => {
            // sorted descending
            let n = rng.gen_range_usize(2, 100);
            let mut v: Vec<i64> = (0..n).map(|_| rng.gen_range_i64(1, 1000)).collect();
            v.sort();
            v.reverse();
            v
        }
        4 => {
            // V-shape (single valley)
            let n = rng.gen_range_usize(3, 100);
            let mid = n / 2;
            (0..n).map(|i| {
                let d = if i <= mid { mid - i } else { i - mid };
                d as i64 + 1
            }).collect()
        }
        5 => {
            // ^-shape (no valley except endpoints)
            let n = rng.gen_range_usize(3, 100);
            let mid = n / 2;
            (0..n).map(|i| {
                let d = if i <= mid { i } else { n - 1 - i };
                d as i64 + 1
            }).collect()
        }
        6 => {
            // moderate-large random small range
            let n = rng.gen_range_usize(500, 2000);
            (0..n).map(|_| rng.gen_range_i64(1, 5)).collect()
        }
        _ => {
            let n = rng.gen_range_usize(2, 200);
            (0..n).map(|_| rng.gen_range_i64(1, 5)).collect()
        }
    }
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(1760);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;
    let mut tries = 0usize;

    while count < target && tries < 100000 {
        tries += 1;
        let t: usize = if count % 5 == 0 { rng.gen_range_usize(2, 20) } else { 1 };
        let mut cases: Vec<TC> = Vec::new();
        for _ in 0..t {
            let mode = (rng.next_u64() as usize) % 8;
            cases.push(gen_case(&mut rng, mode));
        }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let outs = build_output(&cases);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}

