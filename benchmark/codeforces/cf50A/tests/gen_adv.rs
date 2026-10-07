use vstd::prelude::*;

verus! {

pub fn generate_test_case(m_val: u32, n_val: u32) -> (result: (u32, u32))
    requires
        1 <= m_val <= 16,
        1 <= n_val <= 16,
    ensures
        1 <= result.0 <= 16,
        1 <= result.1 <= 16,
{
    (m_val, n_val)
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

    let mut emit = |inp: String, m: u32, n: u32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count { return; }
        if m < 1 || n < 1 || m > n || n > 16 { return; }
        if !seen.insert(inp.clone()) { return; }
        let result = Solution::max_dominoes(m, n);
        let outp = format!("{}\n", result);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    // Cover all (m, n)
    for m in 1u32..=16 {
        for n in m..=16 {
            emit(format!("{} {}\n", m, n), m, n, &mut seen, &mut out, &mut count);
        }
    }

    // Whitespace variants for boundary cases
    let key_pairs = [(1u32,1), (1,16), (2,2), (2,15), (3,3), (8,8), (15,16), (16,16), (1,2), (5,7), (10,10)];
    for &(m,n) in &key_pairs {
        emit(format!("{}  {}\n", m, n), m, n, &mut seen, &mut out, &mut count);
        emit(format!("{}\t{}\n", m, n), m, n, &mut seen, &mut out, &mut count);
        emit(format!(" {} {} \n", m, n), m, n, &mut seen, &mut out, &mut count);
        emit(format!("{} {}", m, n), m, n, &mut seen, &mut out, &mut count);
        emit(format!("{} {}\r\n", m, n), m, n, &mut seen, &mut out, &mut count);
    }

    // Fill rest by repeating with various spacings
    for m in 1u32..=16 {
        for n in m..=16 {
            emit(format!("{}   {}\n", m, n), m, n, &mut seen, &mut out, &mut count);
            if count >= target_count { break; }
            emit(format!("\t{} {}\t\n", m, n), m, n, &mut seen, &mut out, &mut count);
        }
        if count >= target_count { break; }
    }
}

