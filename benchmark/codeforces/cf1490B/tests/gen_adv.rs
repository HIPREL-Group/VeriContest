use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    values: &Vec<i32>,
) -> (a: Vec<i32>)
    requires
        3 <= n <= 30_000,
        n % 3 == 0,
        values.len() == n,
        forall|i: int| 0 <= i < values.len() ==> 0 <= #[trigger] values[i] <= 100,
    ensures
        3 <= a.len() <= 30_000,
        a.len() % 3 == 0,
        forall|i: int| 0 <= i < a.len() ==> 0 <= #[trigger] a[i] <= 100,
{
    let mut a: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            a.len() == i,
            values.len() == n,
            forall|k: int| 0 <= k < values.len() ==> 0 <= #[trigger] values[k] <= 100,
            forall|k: int| 0 <= k < i as int ==> 0 <= #[trigger] a[k] <= 100,
        decreases n - i,
    {
        a.push(values[i]);
        i = i + 1;
    }
    a
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
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let r = (hi as i64 - lo as i64 + 1) as u64;
        (lo as i64 + (self.next_u64() % r) as i64) as i32
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

fn build_output(answers: &[i32]) -> String {
    let mut s = String::new();
    for &a in answers {
        s.push_str(&format!("{}\n", a));
    }
    s
}

fn round_to_3(n: usize) -> usize {
    if n < 3 { 3 } else { (n / 3) * 3 }
}

fn gen_arr(rng: &mut Rng, n: usize, mode: u64) -> Vec<i32> {
    let mut a: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => for _ in 0..n { a.push(0); },
        1 => for _ in 0..n { a.push(1); },
        2 => for _ in 0..n { a.push(2); },
        3 => for i in 0..n { a.push((i % 3) as i32); },
        4 => for _ in 0..n { a.push(100); },
        _ => for _ in 0..n { a.push(rng.gen_range_i32(0, 100)); },
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

    // Big bundle
    {
        let mut cases: Vec<Vec<i32>> = Vec::new();
        for _ in 0..50 {
            let n = round_to_3(rng.gen_range_usize(3, 100));
            let m = rng.next_u64() % 6;
            cases.push(gen_arr(&mut rng, n, m));
        }
        let answers: Vec<i32> = cases.iter().map(|a| Solution::min_moves_balance_remainders(a.clone())).collect();
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
            let n = round_to_3(match rng.next_u64() % 5 {
                0 => 3,
                1 => rng.gen_range_usize(3, 30),
                2 => rng.gen_range_usize(30, 100),
                3 => rng.gen_range_usize(100, 300),
                _ => rng.gen_range_usize(300, 1500),
            });
            if total + n > 50000 { break; }
            total += n;
            let mode = rng.next_u64() % 6;
            cases.push(gen_arr(&mut rng, n, mode));
        }
        if cases.is_empty() { continue; }
        let answers: Vec<i32> = cases.iter().map(|a| Solution::min_moves_balance_remainders(a.clone())).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

