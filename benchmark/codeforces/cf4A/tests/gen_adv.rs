use vstd::prelude::*;

verus! {

pub fn generate_test_case(w: u32) -> (res: u32)
    requires
        1 <= w <= 100,
    ensures
        1 <= res <= 100,
{
    w
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
    let target_count: usize = 200;
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen: HashSet<String> = HashSet::new();
    let mut count = 0usize;

    let mut emit = |inp: String, w: u32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count { return; }
        if w < 1 || w > 100 { return; }
        if !seen.insert(inp.clone()) { return; }
        let result = Solution::can_split_even(w);
        let outp = if result { "YES\n".to_string() } else { "NO\n".to_string() };
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    // All values 1..=100 with various trailing whitespace patterns (main.rs uses .trim())
    for w in 1..=100u32 {
        emit(format!("{}\n", w), w, &mut seen, &mut out, &mut count);
    }
    // Boundary cases with extra whitespace
    let edge_cases = [1u32, 2, 3, 4, 5, 6, 7, 8, 96, 97, 98, 99, 100];
    for &w in &edge_cases {
        emit(format!("{}\n", w), w, &mut seen, &mut out, &mut count);
        emit(format!("{}", w), w, &mut seen, &mut out, &mut count);
        emit(format!(" {} \n", w), w, &mut seen, &mut out, &mut count);
        emit(format!("{}\r\n", w), w, &mut seen, &mut out, &mut count);
        emit(format!("{} \n", w), w, &mut seen, &mut out, &mut count);
        emit(format!("\t{}\t\n", w), w, &mut seen, &mut out, &mut count);
    }

    // Fill remaining
    let mut w = 1u32;
    while count < target_count {
        emit(format!("  {}\n", w), w, &mut seen, &mut out, &mut count);
        if count >= target_count { break; }
        emit(format!("{}\n\n", w), w, &mut seen, &mut out, &mut count);
        w = if w >= 100 { 1 } else { w + 1 };
    }
}

