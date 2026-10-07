use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    s1: i64,
    s2: i64,
    s3: i64,
    s4: i64,
) -> (result: (i64, i64, i64, i64))
    requires
        1 <= s1 <= 100,
        1 <= s2 <= 100,
        1 <= s3 <= 100,
        1 <= s4 <= 100,
        s1 != s2,
        s1 != s3,
        s1 != s4,
        s2 != s3,
        s2 != s4,
        s3 != s4,
    ensures
        ({
            let (a, b, c, d) = result;
            &&& 1 <= a <= 100
            &&& 1 <= b <= 100
            &&& 1 <= c <= 100
            &&& 1 <= d <= 100
            &&& a != b
            &&& a != c
            &&& a != d
            &&& b != c
            &&& b != d
            &&& c != d
        }),
{
    (s1, s2, s3, s4)
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

fn build_input(cases: &[(i64, i64, i64, i64)]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (a, b, c, d) in cases {
        s.push_str(&format!("{} {} {} {}\n", a, b, c, d));
    }
    s
}

fn build_output(answers: &[bool]) -> String {
    let mut s = String::new();
    for &a in answers {
        s.push_str(if a { "YES\n" } else { "NO\n" });
    }
    s
}

fn make_distinct(rng: &mut Rng) -> (i64, i64, i64, i64) {
    loop {
        let s1 = rng.gen_range_i64(1, 100);
        let s2 = rng.gen_range_i64(1, 100);
        let s3 = rng.gen_range_i64(1, 100);
        let s4 = rng.gen_range_i64(1, 100);
        let mut set = HashSet::new();
        set.insert(s1); set.insert(s2); set.insert(s3); set.insert(s4);
        if set.len() == 4 { return (s1, s2, s3, s4); }
    }
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(31337);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    // boundary
    {
        let cases: Vec<(i64, i64, i64, i64)> = vec![
            (1, 2, 3, 4),
            (4, 3, 2, 1),
            (97, 98, 99, 100),
            (100, 99, 98, 97),
        ];
        let answers: Vec<bool> = cases.iter().map(|&(a, b, c, d)| Solution::fair_playoff(a, b, c, d)).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }

    while count < target {
        let t: usize = match count % 5 {
            0 => 1,
            1 => rng.gen_range_usize(2, 10),
            2 => rng.gen_range_usize(10, 50),
            3 => rng.gen_range_usize(50, 100),
            _ => rng.gen_range_usize(100, 500),
        };
        let mut cases: Vec<(i64, i64, i64, i64)> = Vec::new();
        for _ in 0..t {
            cases.push(make_distinct(&mut rng));
        }
        let answers: Vec<bool> = cases.iter().map(|&(a, b, c, d)| Solution::fair_playoff(a, b, c, d)).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

