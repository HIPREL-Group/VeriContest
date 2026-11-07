use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32) -> (res: i32)
    requires
        1000 <= n <= 9000,
    ensures
        1000 <= res <= 9000,
{
    n
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

fn build_input(y: i32) -> String {
    format!("{}\n", y)
}

fn build_output(ans: i32) -> String {
    format!("{}\n", ans)
}

fn main() {
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;
    let target = 200;

    // Enumerate all years: 1000 to 9000 inclusive (8001 values)
    // Just take first 200 unique
    let mut step = (9000 - 1000 + 1) / target;
    if step == 0 { step = 1; }
    let mut y = 1000;
    while y <= 9000 && count < target {
        let inp = build_input(y);
        if !seen.insert(inp.clone()) {
            y += step as i32;
            continue;
        }
        let ans = Solution::beautiful_year(y);
        let outp = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
        y += step as i32;
    }

    // Fill remaining
    let mut y = 1000;
    while count < target && y <= 9000 {
        let inp = build_input(y);
        if seen.insert(inp.clone()) {
            let ans = Solution::beautiful_year(y);
            let outp = build_output(ans);
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
            count += 1;
        }
        y += 1;
    }
}

