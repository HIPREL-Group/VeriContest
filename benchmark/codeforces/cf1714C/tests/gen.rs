use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: u32) -> (result: u32)
    requires
        1 <= seed <= 45,
    ensures
        1 <= result <= 45,
{
    seed
}

}

use std::io::Write;
use std::collections::HashSet;

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
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut seen: HashSet<String> = HashSet::new();
    let mut count = 0usize;
    let target: usize = 100;

    // Single-test cases first
    for s in 1..=45u32 {
        if count >= target { break; }
        let result = Solution::min_varied(s);
        let inp = format!("1\n{}\n", s);
        let outp = format!("{}\n", result);
        if !seen.insert(inp.clone()) { continue; }
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
    // Multi-test cases to fill up to 100
    for a in 1..=45u32 {
        if count >= target { break; }
        for b in 1..=45u32 {
            if count >= target { break; }
            let ra = Solution::min_varied(a);
            let rb = Solution::min_varied(b);
            let inp = format!("2\n{}\n{}\n", a, b);
            let outp = format!("{}\n{}\n", ra, rb);
            if !seen.insert(inp.clone()) { continue; }
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
            count += 1;
        }
    }
}
