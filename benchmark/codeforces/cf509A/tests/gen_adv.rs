use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: u32) -> (res: u32)
    requires
        1 <= n <= 10,
    ensures
        1 <= res <= 10,
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

fn main() {
    let target_count: usize = 200;
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen: HashSet<String> = HashSet::new();
    let mut count = 0usize;

    let mut emit = |inp: String, n: u32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count { return; }
        if !(1 <= n && n <= 10) { return; }
        if !seen.insert(inp.clone()) { return; }
        let result = Solution::max_in_table(n);
        let outp = format!("{}\n", result);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    // Generate enough unique whitespace patterns
    for n in 1u32..=10 {
        for prefix_spaces in 0..5 {
            for suffix_spaces in 0..5 {
                for trail in 0..3 {
                    let mut inp = " ".repeat(prefix_spaces);
                    inp.push_str(&n.to_string());
                    inp.push_str(&" ".repeat(suffix_spaces));
                    inp.push_str(&"\n".repeat(trail));
                    if !inp.is_empty() {
                        emit(inp, n, &mut seen, &mut out, &mut count);
                        if count >= target_count { break; }
                    }
                }
                if count >= target_count { break; }
            }
            if count >= target_count { break; }
        }
        if count >= target_count { break; }
    }
    // Fallback
    for n in 1u32..=10 {
        if count >= target_count { break; }
        for k in 0..50 {
            if count >= target_count { break; }
            let mut inp = "\t".repeat(k % 3);
            inp.push_str(&n.to_string());
            inp.push_str(&" ".repeat(k));
            inp.push('\n');
            emit(inp, n, &mut seen, &mut out, &mut count);
        }
    }
}
