use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: usize, events: Vec<i32>) -> (res: (usize, Vec<i32>))
    requires
        1 <= n <= 100000,
        events.len() == n,
        forall|i: int| 0 <= i < events.len() ==> #[trigger] events[i] as int == -1 || (1 <= events[i] as int <= 10),
    ensures
        1 <= res.0 <= 100000,
        res.1.len() == res.0,
        forall|i: int| 0 <= i < res.1.len() ==> #[trigger] res.1[i] as int == -1 || (1 <= res.1[i] as int <= 10),
{
    (n, events)
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

fn build_input(n: usize, events: &[i32], sep1: &str, sep2: &str, sep3: &str) -> String {
    let parts: Vec<String> = events.iter().map(|x| x.to_string()).collect();
    format!("{}{}{}{}", n, sep1, parts.join(sep2), sep3)
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(4271);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |inp: String, n: usize, events: &Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if !seen.insert(inp.clone()) { return; }
        let result = Solution::count_untreated(n, events.clone());
        let outp = format!("{}\n", result);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    while count < target {
        let n = rng.gen_range_usize(1, 200);
        let events: Vec<i32> = (0..n).map(|_| {
            let r = rng.next_u64() % 11;
            if r == 0 { -1 } else { r as i32 }
        }).collect();
        let mode = (rng.next_u64() % 6) as usize;
        let inp = match mode {
            0 => build_input(n, &events, "\n", " ", "\n"),
            1 => build_input(n, &events, "\n", " ", ""),
            2 => build_input(n, &events, " ", " ", "\n"),
            3 => build_input(n, &events, "\n", "\t", "\n"),
            4 => build_input(n, &events, "\r\n", " ", "\r\n"),
            _ => build_input(n, &events, "\n", "\n", "\n"),
        };
        emit(inp, n, &events, &mut seen, &mut out, &mut count);
    }
}
