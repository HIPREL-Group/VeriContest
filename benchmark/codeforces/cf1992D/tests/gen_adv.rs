use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_a: Vec<u8>, m: usize, k: i64) -> (result: (Vec<u8>, usize, i64))
    requires
        1 <= seed_a.len() <= 50,
        1 <= m <= 10,
        0 <= k <= 200_000,
        forall |i: int| 0 <= i < seed_a.len() ==> #[trigger] seed_a[i] <= 2u8,
    ensures
        1 <= result.0.len() <= 200_000,
        1 <= result.1 <= 10,
        0 <= result.2 <= 200_000,
        forall |i: int| 0 <= i < result.0.len() ==> #[trigger] result.0[i] <= 2u8,
{
    (seed_a, m, k)
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
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
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

fn vec_to_str(v: &Vec<u8>) -> String {
    let mut s = String::with_capacity(v.len());
    for x in v {
        s.push(match x {
            0 => 'W',
            1 => 'C',
            2 => 'L',
            _ => 'W',
        });
    }
    s
}

fn build_input(cases: &[(Vec<u8>, usize, i64)]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (a, m, k) in cases {
        s.push_str(&format!("{} {} {}\n", a.len(), m, k));
        s.push_str(&format!("{}\n", vec_to_str(a)));
    }
    s
}

fn build_output(answers: &[bool]) -> String {
    let mut s = String::new();
    for ans in answers {
        s.push_str(if *ans { "YES\n" } else { "NO\n" });
    }
    s
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(0x1992D);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut count = 0usize;
    let mut seen = HashSet::new();

    while count < target {
        let t: usize = if count < 20 { 1 }
                       else if count < 80 { rng.gen_range_usize(2, 6) }
                       else if count < 150 { rng.gen_range_usize(3, 10) }
                       else { rng.gen_range_usize(5, 15) };
        let mut cases: Vec<(Vec<u8>, usize, i64)> = Vec::with_capacity(t);
        for _ in 0..t {
            let n = rng.gen_range_usize(1, 50);
            let m = rng.gen_range_usize(1, 10);
            let k = rng.gen_range_i64(0, 50);
            let seed_a: Vec<u8> = (0..n).map(|_| (rng.next_u64() % 3) as u8).collect();
            let (a, mm, kk) = generate_test_case(seed_a, m, k);
            cases.push((a, mm, kk));
        }
        let answers: Vec<bool> = cases.iter().map(|(a, m, k)| Solution::can_cross(a.clone(), *m, *k)).collect();
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}
