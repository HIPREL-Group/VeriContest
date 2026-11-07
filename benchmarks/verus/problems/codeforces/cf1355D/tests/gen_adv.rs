use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i64, s: i64) -> (result: (i64, i64))
    requires
        1 <= n <= s <= 1_000_000,
    ensures
        result.0 == n,
        result.1 == s,
        1 <= result.0 <= result.1 <= 1_000_000,
{
    (n, s)
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
    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let r = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % r) as i128) as i64
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

fn build_input(n: i64, s: i64) -> String {
    format!("{} {}\n", n, s)
}

fn build_output(r: &Option<(Vec<i64>, i64)>) -> String {
    match r {
        None => "NO\n".to_string(),
        Some((a, k)) => {
            let mut out = String::from("YES\n");
            let parts: Vec<String> = a.iter().map(|x| x.to_string()).collect();
            out.push_str(&parts.join(" "));
            out.push('\n');
            out.push_str(&format!("{}\n", k));
            out
        }
    }
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(31337);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    // Boundary cases
    for n in [1i64, 2, 3, 5, 10, 100, 1000, 10_000, 100_000, 999_999, 1_000_000] {
        for ds in [0i64, -1, 1, -2, 2] {
            let s_target = 2 * n + ds;
            if s_target >= n && s_target <= 1_000_000 && s_target >= 1 {
                let r = Solution::construct_game(n, s_target);
                let inp = build_input(n, s_target);
                let outp = build_output(&r);
                writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
                count += 1;
            }
        }
    }

    while count < target {
        let mode = rng.next_u64() % 8;
        let (n, s): (i64, i64) = match mode {
            0 => {
                let n = rng.gen_range_i64(1, 10);
                let s = rng.gen_range_i64(n, n + 10);
                (n, s)
            }
            1 => {
                let n = rng.gen_range_i64(1, 100);
                let s = rng.gen_range_i64(n, n.saturating_mul(3));
                (n, s)
            }
            2 => {
                let n = rng.gen_range_i64(1, 1000);
                let s = rng.gen_range_i64(n, n.saturating_mul(5).min(1_000_000));
                (n, s)
            }
            3 => {
                let n = rng.gen_range_i64(500_000, 1_000_000);
                let s = rng.gen_range_i64(n, 1_000_000);
                (n, s)
            }
            4 => {
                let n = rng.gen_range_i64(1, 500_000);
                (n, 2 * n)
            }
            5 => {
                let n = rng.gen_range_i64(1, 500_000);
                let s = (2 * n - 1).max(n);
                (n, s)
            }
            6 => {
                let n = rng.gen_range_i64(1, 1_000_000);
                (n, n)
            }
            _ => {
                let n = rng.gen_range_i64(1, 100_000);
                let s = rng.gen_range_i64(n, 1_000_000);
                (n, s)
            }
        };
        let r = Solution::construct_game(n, s);
        let inp = build_input(n, s);
        let outp = build_output(&r);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

