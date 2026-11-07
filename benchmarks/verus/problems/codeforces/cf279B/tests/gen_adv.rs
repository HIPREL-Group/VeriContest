use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    t_val: i64,
    books: Vec<i32>,
) -> (result: (Vec<i32>, i64))
    requires
        1 <= n <= 100_000,
        books.len() == n,
        1 <= t_val <= 1_000_000_000,
        forall|i: int| 0 <= i < books@.len() ==> 1 <= #[trigger] books@[i] <= 10_000,
    ensures
        1 <= result.0.len() <= 100_000,
        1 <= result.1 <= 1_000_000_000,
        forall|i: int| 0 <= i < result.0@.len() ==> 1 <= #[trigger] result.0@[i] <= 10_000,
{
    (books, t_val)
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

fn build_input(books: &[i32], t: i64) -> String {
    let mut s = format!("{} {}\n", books.len(), t);
    let parts: Vec<String> = books.iter().map(|x| x.to_string()).collect();
    s.push_str(&parts.join(" "));
    s.push('\n');
    s
}

fn build_output(ans: usize) -> String {
    format!("{}\n", ans)
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(0x279BB);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut tries = 0;
    while count < target && tries < target * 100 {
        tries += 1;
        let n = match tries % 6 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(2, 50),
            2 => rng.gen_range_usize(50, 500),
            3 => rng.gen_range_usize(500, 5000),
            4 => rng.gen_range_usize(5000, 50000),
            _ => rng.gen_range_usize(50000, 100000),
        };
        let t = rng.gen_range_i64(1, 1_000_000_000);
        let books: Vec<i32> = (0..n).map(|_| rng.gen_range_i64(1, 10000) as i32).collect();
        let inp = build_input(&books, t);
        if !seen.insert(inp.clone()) { continue; }
        let ans = Solution::max_books_read(books, t);
        let outp = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

