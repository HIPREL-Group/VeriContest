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
    let target_count: usize = 100;
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut count = 0usize;

    let mut emit = |inp: String, n: u32, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count { return; }
        if !(1 <= n && n <= 10) { return; }
        let result = Solution::max_in_table(n);
        let outp = format!("{}\n", result);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    // All values 1..=10, repeated with various separators
    for n in 1u32..=10 {
        emit(format!("{}\n", n), n, &mut out, &mut count);
    }
    for n in 1u32..=10 {
        emit(format!("{}", n), n, &mut out, &mut count);
        emit(format!(" {}\n", n), n, &mut out, &mut count);
        emit(format!("{} \n", n), n, &mut out, &mut count);
        emit(format!(" {} \n", n), n, &mut out, &mut count);
        emit(format!("{}\r\n", n), n, &mut out, &mut count);
        emit(format!("{}\t\n", n), n, &mut out, &mut count);
    }
    while count < target_count {
        for n in 1u32..=10 {
            if count >= target_count { break; }
            emit(format!("\t{}\n", n), n, &mut out, &mut count);
            if count >= target_count { break; }
            emit(format!("{}\n\n", n), n, &mut out, &mut count);
        }
    }
}
