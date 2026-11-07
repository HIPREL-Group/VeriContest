use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i64) -> (res: i64)
    requires
        1 <= n <= 1000000000000000,
    ensures
        1 <= res <= 1000000000000000,
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

    let mut emit = |inp: String, n: i64, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count { return; }
        if n < 1 || n > 1000000000000000 { return; }
        if !seen.insert(inp.clone()) { return; }
        let result = Solution::calculating_function(n);
        let outp = format!("{}\n", result);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    for n in 1i64..=120 {
        emit(format!("{}\n", n), n, &mut seen, &mut out, &mut count);
    }
    let edges = [1i64, 2, 3, 4, 5, 100, 1000, 1000000, 1000000000, 999999999999999, 1000000000000000];
    for &n in &edges {
        emit(format!("{}\n", n), n, &mut seen, &mut out, &mut count);
        emit(format!("{}", n), n, &mut seen, &mut out, &mut count);
        emit(format!(" {} \n", n), n, &mut seen, &mut out, &mut count);
        emit(format!("{}\r\n", n), n, &mut seen, &mut out, &mut count);
        emit(format!("{} \n", n), n, &mut seen, &mut out, &mut count);
    }
    let mut n: i64 = 1;
    while count < target_count {
        emit(format!("  {}\n", n), n, &mut seen, &mut out, &mut count);
        if count >= target_count { break; }
        emit(format!("{}\n\n", n), n, &mut seen, &mut out, &mut count);
        n = if n >= 1000000000000000 { 1 } else { n + 1 };
    }
}
