use vstd::prelude::*;

verus! {

pub fn generate_test_case(k: i32, l: i32, m: i32, n: i32, d: i32) -> (result: (i32, i32, i32, i32, i32))
    requires
        1 <= k <= 10,
        1 <= l <= 10,
        1 <= m <= 10,
        1 <= n <= 10,
        1 <= d <= 100_000,
    ensures
        ({
            let (kk, ll, mm, nn, dd) = result;
            1 <= kk <= 10 && 1 <= ll <= 10 && 1 <= mm <= 10 && 1 <= nn <= 10 && 1 <= dd <= 100_000
        }),
{
    (k, l, m, n, d)
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

fn build_input(k: i32, l: i32, m: i32, n: i32, d: i32) -> String {
    format!("{}\n{}\n{}\n{}\n{}\n", k, l, m, n, d)
}

fn build_output(ans: i32) -> String {
    format!("{}\n", ans)
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(31337);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);

    let mut emit = |k: i32, l: i32, m: i32, n: i32, d: i32, out: &mut std::io::BufWriter<std::fs::File>| {
        let ans = Solution::count_damaged(k, l, m, n, d);
        let inp = build_input(k, l, m, n, d);
        let outp = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
    };

    // Boundary cases
    for k in 1i32..=10 {
        if k > 5 && k < 10 { continue; }  // skip middle
        for d in [1, 10, 100, 1000, 10000, 100000] {
            emit(k, k, k, k, d, &mut out);
        }
    }

    let mut count = 0usize;
    let p = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let s = std::fs::read_to_string(&p).unwrap();
    count = s.lines().count();

    while count < target {
        let mode = rng.next_u64() % 5;
        let (k, l, m, n, d) = match mode {
            0 => (1, 1, 1, 1, rng.gen_range_i32(1, 100000)),
            1 => (10, 10, 10, 10, rng.gen_range_i32(1, 100000)),
            2 => {
                (rng.gen_range_i32(1, 10),
                 rng.gen_range_i32(1, 10),
                 rng.gen_range_i32(1, 10),
                 rng.gen_range_i32(1, 10),
                 100000)
            }
            3 => {
                (rng.gen_range_i32(1, 10),
                 rng.gen_range_i32(1, 10),
                 rng.gen_range_i32(1, 10),
                 rng.gen_range_i32(1, 10),
                 1)
            }
            _ => {
                (rng.gen_range_i32(1, 10),
                 rng.gen_range_i32(1, 10),
                 rng.gen_range_i32(1, 10),
                 rng.gen_range_i32(1, 10),
                 rng.gen_range_i32(1, 100000))
            }
        };
        emit(k, l, m, n, d, &mut out);
        count += 1;
    }
}

