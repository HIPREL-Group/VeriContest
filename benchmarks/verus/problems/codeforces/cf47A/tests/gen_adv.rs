use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: u32) -> (res: u32)
    requires
        1 <= n <= 500,
    ensures
        1 <= res <= 500,
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
        if !(1 <= n && n <= 500) { return; }
        if !seen.insert(inp.clone()) { return; }
        let result = Solution::is_triangular(n);
        let outp = if result { "YES\n".to_string() } else { "NO\n".to_string() };
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    for n in 1u32..=120 {
        emit(format!("{}\n", n), n, &mut seen, &mut out, &mut count);
    }
    let edges: Vec<u32> = (1u32..32).map(|k| k*(k+1)/2).collect();
    for &n in &edges {
        emit(format!("{}\n", n), n, &mut seen, &mut out, &mut count);
        emit(format!("{}", n), n, &mut seen, &mut out, &mut count);
        emit(format!(" {} \n", n), n, &mut seen, &mut out, &mut count);
        emit(format!("{}\r\n", n), n, &mut seen, &mut out, &mut count);
        emit(format!("{} \n", n), n, &mut seen, &mut out, &mut count);
    }
    let mut n: u32 = 1;
    while count < target_count {
        emit(format!("  {}\n", n), n, &mut seen, &mut out, &mut count);
        if count >= target_count { break; }
        emit(format!("{}\n\n", n), n, &mut seen, &mut out, &mut count);
        n = if n >= 500 { 1 } else { n + 1 };
    }
}
