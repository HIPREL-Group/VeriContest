use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: u32, m: u32) -> (res: (u32, u32))
    requires
        1 <= n <= 50,
        1 <= m <= 10000,
    ensures
        1 <= res.0 <= 50,
        1 <= res.1 <= 10000,
{
    (n, m)
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
    fn gen_range_u32(&mut self, lo: u32, hi: u32) -> u32 {
        lo + (self.next_u64() as u32) % (hi - lo + 1)
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

fn main() {
    let target_count: usize = 200;
    let mut rng = Rng::new(921);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen: HashSet<String> = HashSet::new();
    let mut count = 0usize;

    let mut emit = |inp: String, n: u32, m: u32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count { return; }
        if !(1 <= n && n <= 50 && 1 <= m && m <= 10000) { return; }
        if !seen.insert(inp.clone()) { return; }
        let result = Solution::presenter_chips(n, m);
        let outp = format!("{}\n", result);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    while count < target_count {
        let n = rng.gen_range_u32(1, 50);
        let m = rng.gen_range_u32(1, 10000);
        let mode = (rng.next_u64() % 6) as usize;
        let inp = match mode {
            0 => format!("{} {}\n", n, m),
            1 => format!("{} {}", n, m),
            2 => format!(" {}  {} \n", n, m),
            3 => format!("{}\t{}\n", n, m),
            4 => format!("{} {}\r\n", n, m),
            _ => format!("{}\n{}\n", n, m),
        };
        emit(inp, n, m, &mut seen, &mut out, &mut count);
    }
}
