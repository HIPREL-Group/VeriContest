use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: usize, d: Vec<u32>, a: usize, b: usize) -> (res: (usize, Vec<u32>, usize, usize))
    requires
        2 <= n <= 100,
        d.len() == n - 1,
        forall|i: int| 0 <= i < d.len() ==> 1 <= #[trigger] d[i] as int <= 100,
        1 <= a < b <= n,
    ensures
        2 <= res.0 <= 100,
        res.1.len() == res.0 - 1,
        forall|i: int| 0 <= i < res.1.len() ==> 1 <= #[trigger] res.1[i] as int <= 100,
        1 <= res.2 < res.3 <= res.0,
{
    (n, d, a, b)
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
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        lo + (self.next_u64() as usize) % (hi - lo + 1)
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

fn build_input(n: usize, d: &[u32], a: usize, b: usize, sep1: &str, sep2: &str, sep3: &str) -> String {
    let parts: Vec<String> = d.iter().map(|x| x.to_string()).collect();
    format!("{}{}{}{}{} {}{}", n, sep1, parts.join(" "), sep2, a, b, sep3)
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(381);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |inp: String, n: usize, d: &Vec<u32>, a: usize, b: usize, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if !seen.insert(inp.clone()) { return; }
        let result = Solution::years_needed(n, d.clone(), a, b);
        let outp = format!("{}\n", result);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    // Random with various whitespace
    while count < target {
        let n = rng.gen_range_usize(2, 100);
        let d: Vec<u32> = (0..n-1).map(|_| rng.gen_range_u32(1, 100)).collect();
        let a = rng.gen_range_usize(1, n - 1);
        let b = rng.gen_range_usize(a + 1, n);
        let mode = (rng.next_u64() % 6) as usize;
        let inp = match mode {
            0 => build_input(n, &d, a, b, "\n", "\n", "\n"),
            1 => build_input(n, &d, a, b, "\n", "\n", ""),
            2 => build_input(n, &d, a, b, " ", " ", "\n"),
            3 => build_input(n, &d, a, b, "\n", "\n", " \n"),
            4 => build_input(n, &d, a, b, "\r\n", "\r\n", "\r\n"),
            _ => build_input(n, &d, a, b, "\t", "\t", "\n"),
        };
        emit(inp, n, &d, a, b, &mut seen, &mut out, &mut count);
    }
}
