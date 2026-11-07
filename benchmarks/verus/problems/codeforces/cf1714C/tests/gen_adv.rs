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
    let target: usize = 200;
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut seen: HashSet<String> = HashSet::new();
    let mut count = 0usize;

    let mut emit = |inp: String, s: u32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if s < 1 || s > 45 { return; }
        if !seen.insert(inp.clone()) { return; }
        let result = Solution::min_varied(s);
        let outp = format!("{}\n", result);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    // All values 1..=45 with various trailing whitespace patterns
    for s in 1..=45u32 {
        emit(format!("1\n{}\n", s), s, &mut seen, &mut out, &mut count);
    }
    // Different whitespace formats
    for s in 1..=45u32 {
        emit(format!("1\n{}", s), s, &mut seen, &mut out, &mut count);
        emit(format!("1\n {} \n", s), s, &mut seen, &mut out, &mut count);
        emit(format!("1\n{} \n", s), s, &mut seen, &mut out, &mut count);
        emit(format!("1\n\t{}\t\n", s), s, &mut seen, &mut out, &mut count);
    }
    // Multi-test cases
    let mut s = 1u32;
    while count < target {
        emit(format!("2\n{}\n{}\n", s, ((s % 45) + 1)), s, &mut seen, &mut out, &mut count);
        s = if s >= 45 { 1 } else { s + 1 };
    }
}
