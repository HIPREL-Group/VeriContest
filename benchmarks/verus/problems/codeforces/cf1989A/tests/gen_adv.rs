use vstd::prelude::*;

verus! {

pub fn generate_test_case(x: i32, y: i32) -> (result: (i32, i32))
    requires
        -50 <= x <= 50,
        -50 <= y <= 50,
        !(x == 0 && y == 0),
    ensures
        -50 <= result.0 <= 50,
        -50 <= result.1 <= 50,
        !(result.0 == 0 && result.1 == 0),
{
    (x, y)
}

}

use std::io::Write;
use std::collections::HashSet;

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }

    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
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

fn build_input(coins: &[(i32, i32)]) -> String {
    let mut s = format!("{}\n", coins.len());
    for &(x, y) in coins {
        s.push_str(&format!("{} {}\n", x, y));
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

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(1);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut count = 0usize;

    while count < target {
        let n: usize = if count < 30 { rng.gen_range_usize(1, 10) }
                       else if count < 100 { rng.gen_range_usize(50, 200) }
                       else { rng.gen_range_usize(200, 500) };
        let mut used: HashSet<(i32, i32)> = HashSet::new();
        let mut coins: Vec<(i32, i32)> = Vec::with_capacity(n);
        let mode = count % 5;
        let max_attempts = n * 30 + 100;
        let mut tries = 0;
        while coins.len() < n && tries < max_attempts {
            tries += 1;
            let (x, y) = match mode {
                0 => (rng.gen_range_i64(-50, 50) as i32, -1i32),
                1 => (rng.gen_range_i64(-50, 50) as i32, rng.gen_range_i64(-3, 3) as i32),
                2 => (rng.gen_range_i64(-50, 50) as i32, rng.gen_range_i64(-50, 50) as i32),
                3 => (rng.gen_range_i64(-50, 50) as i32, rng.gen_range_i64(-50, -2) as i32),
                _ => (rng.gen_range_i64(-50, 50) as i32, rng.gen_range_i64(0, 50) as i32),
            };
            if x == 0 && y == 0 { continue; }
            if used.insert((x, y)) { coins.push((x, y)); }
        }
        if coins.is_empty() { continue; }
        let key = format!("{:?}", coins);
        if !seen.insert(key) { continue; }
        let answers: Vec<bool> = coins.iter().map(|&(x, y)| Solution::can_catch_coin(x, y)).collect();
        let inp = build_input(&coins);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

