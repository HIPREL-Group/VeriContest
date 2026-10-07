use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: u32) -> (result: u32)
    requires 1 <= n <= 100,
    ensures 1 <= result <= 100,
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

fn build_output(ans: &Option<Vec<u32>>) -> String {
    match ans {
        None => "-1\n".to_string(),
        Some(v) => {
            let parts: Vec<String> = v.iter().map(|x| x.to_string()).collect();
            format!("{}\n", parts.join(" "))
        }
    }
}

fn main() {
    let target: usize = 200;
    let mut seen: HashSet<String> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |inp: String, n: u32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if !(1 <= n && n <= 100) { return; }
        if !seen.insert(inp.clone()) { return; }
        let ans = Solution::perfect_permutation(n);
        let outp = build_output(&ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    // All values 1..=100 with various trailing whitespace
    for n in 1u32..=100 {
        emit(format!("{}\n", n), n, &mut seen, &mut out, &mut count);
    }
    let edge = [1u32, 2, 3, 4, 5, 6, 99, 100];
    for &n in &edge {
        emit(format!("{}", n), n, &mut seen, &mut out, &mut count);
        emit(format!(" {} \n", n), n, &mut seen, &mut out, &mut count);
        emit(format!("{}\r\n", n), n, &mut seen, &mut out, &mut count);
        emit(format!("\t{}\t\n", n), n, &mut seen, &mut out, &mut count);
        emit(format!("{} \n", n), n, &mut seen, &mut out, &mut count);
    }
    // Fill more
    let mut idx: u32 = 1;
    while count < target {
        emit(format!("  {}\n", idx), idx, &mut seen, &mut out, &mut count);
        if count >= target { break; }
        emit(format!("{}\n\n", idx), idx, &mut seen, &mut out, &mut count);
        idx = if idx >= 100 { 1 } else { idx + 1 };
    }
}
