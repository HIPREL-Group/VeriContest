use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    raw_a: Vec<i32>,
) -> (result: (Vec<i32>, usize))
    requires
        1 <= n <= 100,
        raw_a.len() == n,
        forall|i: int| 0 <= i < raw_a.len() ==> -100 <= #[trigger] raw_a[i] as int <= 100,
    ensures
        1 <= result.1 <= 100,
        result.0.len() == result.1,
        forall|i: int| 0 <= i < result.0.len() ==> -100 <= #[trigger] result.0[i] as int <= 100,
{
    (raw_a, n)
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
        let range = (hi - lo + 1) as u64;
        lo + (self.next_u64() % range) as i64
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

fn build_input(a: &Vec<i32>) -> String {
    let n = a.len();
    let mut s = format!("{}\n", n);
    for i in 0..n {
        if i > 0 { s.push(' '); }
        s.push_str(&format!("{}", a[i]));
    }
    s.push('\n');
    s
}

fn build_output(ans: &Option<i32>) -> String {
    match ans {
        Some(v) => format!("{}\n", v),
        None => "NO\n".to_string(),
    }
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(0x22AA);
    let mut seen: HashSet<String> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut tries = 0usize;
    while count < target && tries < target * 200 {
        tries += 1;
        let n = match tries % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(5, 20),
            2 => rng.gen_range_usize(20, 50),
            3 => rng.gen_range_usize(50, 100),
            _ => rng.gen_range_usize(1, 100),
        };
        let mode = tries % 4;
        let a: Vec<i32> = match mode {
            0 => (0..n).map(|_| rng.gen_range_i64(-100, 100) as i32).collect(),
            1 => vec![5i32; n],
            2 => (0..n).map(|i| (i as i32) - 50).collect(),
            _ => (0..n).map(|_| rng.gen_range_i64(-5, 5) as i32).collect(),
        };
        let inp = build_input(&a);
        if !seen.insert(inp.clone()) { continue; }
        let ans = Solution::second_min(a, n);
        let outp = build_output(&ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}
