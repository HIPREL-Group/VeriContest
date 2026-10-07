use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    choices: &Vec<u8>,
) -> (result: (usize, Vec<i32>))
    requires
        1 <= n <= 100,
        choices.len() == n,
        forall|i: int| 0 <= i < choices.len() ==> (#[trigger] choices[i] == 0u8 || choices[i] == 1u8),
    ensures
        result.0 == n,
        1 <= result.0 <= 100,
        result.1.len() == n,
        forall|i: int| 0 <= i < result.1.len() ==> (#[trigger] result.1@[i] == 1i32 || result.1@[i] == 2i32),
{
    let mut a: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == choices.len(),
            1 <= n <= 100,
            0 <= i <= n,
            a.len() == i,
            forall|k: int| 0 <= k < choices.len() ==> (#[trigger] choices[k] == 0u8 || choices[k] == 1u8),
            forall|k: int| 0 <= k < a.len() ==> (#[trigger] a@[k] == 1i32 || a@[k] == 2i32),
        decreases n - i,
    {
        let c = choices[i];
        if c == 0u8 {
            a.push(1i32);
        } else {
            a.push(2i32);
        }
        i = i + 1;
    }
    (n, a)
}

}

use std::io::Write;

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

fn build_input(cases: &[Vec<i32>]) -> String {
    let mut s = format!("{}\n", cases.len());
    for a in cases {
        s.push_str(&format!("{}\n", a.len()));
        let parts: Vec<String> = a.iter().map(|x| x.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
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

fn gen_arr(rng: &mut Rng, n: usize, mode: u64) -> Vec<i32> {
    let mut a: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => for _ in 0..n { a.push(1); },
        1 => for _ in 0..n { a.push(2); },
        2 => for i in 0..n { a.push(if i % 2 == 0 { 1 } else { 2 }); },
        3 => { // half 1s half 2s
            for i in 0..n { a.push(if i < n / 2 { 1 } else { 2 }); }
        }
        4 => { // odd number of 1s
            for i in 0..n { a.push(if i < 3 { 1 } else { 2 }); }
        }
        _ => for _ in 0..n { a.push(if rng.next_u64() % 2 == 0 { 1 } else { 2 }); },
    }
    a
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(31337);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);

    let mut count = 0usize;

    // Big bundle, all sizes, etc
    {
        let cases: Vec<Vec<i32>> = (0..50).map(|i| if i % 2 == 0 { vec![1; 100] } else { vec![2; 100] }).collect();
        let answers: Vec<bool> = cases.iter().map(|a| Solution::fair_division(a.len(), a.clone())).collect();
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
            3 => rng.gen_range_usize(50, 200),
            _ => rng.gen_range_usize(200, 1000),
        };
        let mut cases: Vec<Vec<i32>> = Vec::new();
        let mut total = 0;
        for _ in 0..t {
            let n = match rng.next_u64() % 5 {
                0 => 1,
                1 => rng.gen_range_usize(1, 5),
                2 => rng.gen_range_usize(5, 20),
                3 => rng.gen_range_usize(20, 50),
                _ => rng.gen_range_usize(50, 100),
            };
            if total + n > 50000 { break; }
            total += n;
            let mode = rng.next_u64() % 6;
            cases.push(gen_arr(&mut rng, n, mode));
        }
        if cases.is_empty() { continue; }
        let answers: Vec<bool> = cases.iter().map(|a| Solution::fair_division(a.len(), a.clone())).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

