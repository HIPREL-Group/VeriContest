use vstd::prelude::*;

verus! {

pub fn generate_test_case(a: i32, b: i32) -> (result: (i32, i32))
    requires
        1 <= a <= 6,
        1 <= b <= 6,
    ensures
        1 <= result.0 <= 6,
        1 <= result.1 <= 6,
{
    (a, b)
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
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut seen = HashSet::new();
    let mut count = 0usize;
    let target = 200usize;

    let pairs: Vec<(i32, i32)> = (1..=6).flat_map(|a| (1..=6).map(move |b| (a, b))).collect();
    let formats: Vec<Box<dyn Fn(i32, i32) -> String>> = vec![
        Box::new(|a, b| format!("{} {}\n", a, b)),
        Box::new(|a, b| format!("{}  {}\n", a, b)),
        Box::new(|a, b| format!("{}\t{}\n", a, b)),
        Box::new(|a, b| format!("{} {}\n\n", a, b)),
        Box::new(|a, b| format!(" {} {} \n", a, b)),
        Box::new(|a, b| format!("{} {}", a, b)),
        Box::new(|a, b| format!("{}\n{}\n", a, b)),
        Box::new(|a, b| format!("{}     {}\n", a, b)),
        Box::new(|a, b| format!("\n{} {}\n", a, b)),
        Box::new(|a, b| format!("{} {}\r\n", a, b)),
    ];
    'outer: for fmt in &formats {
        for &(a, b) in &pairs {
            if count >= target { break 'outer; }
            let inp = fmt(a, b);
            let key = format!("{:?}", inp);
            if !seen.insert(key) { continue; }
            let (fw, d, sw) = Solution::dice_outcomes(a, b);
            let outs = format!("{} {} {}\n", fw, d, sw);
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
            count += 1;
        }
    }
}

