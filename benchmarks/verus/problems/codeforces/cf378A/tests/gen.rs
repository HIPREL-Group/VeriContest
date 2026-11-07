use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    seed_a: i32,
    seed_b: i32,
    mutation_kind: u8,
) -> (result: (i32, i32))
    requires
        1 <= seed_a <= 6,
        1 <= seed_b <= 6,
    ensures
        1 <= result.0 <= 6,
        1 <= result.1 <= 6,
{
    if mutation_kind == 0 {
        (seed_a, seed_b)                        // identity
    } else if mutation_kind == 1 {
        (seed_b, seed_a)                        // swap
    } else if mutation_kind == 2 {
        (seed_a, seed_a)                        // equal values
    } else if mutation_kind == 3 && seed_a < 6 {
        (seed_a + 1, seed_b)                    // nudge a up
    } else if mutation_kind == 4 && seed_a > 1 {
        (seed_a - 1, seed_b)                    // nudge a down
    } else if mutation_kind == 5 && seed_b < 6 {
        (seed_a, seed_b + 1)                    // nudge b up
    } else if mutation_kind == 6 && seed_b > 1 {
        (seed_a, seed_b - 1)                    // nudge b down
    } else if mutation_kind == 7 {
        (1, 6)                                  // boundary: min, max
    } else if mutation_kind == 8 {
        (6, 1)                                  // boundary: max, min
    } else if mutation_kind == 9 {
        (1, 1)                                  // boundary: both min
    } else if mutation_kind == 10 {
        (6, 6)                                  // boundary: both max
    } else {
        (seed_a, seed_b)                        // fallback
    }
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
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let pairs: Vec<(i32, i32)> = (1..=6).flat_map(|a| (1..=6).map(move |b| (a, b))).collect();
    for &(a, b) in &pairs {
        let key = format!("{} {}", a, b);
        if !seen.insert(key) { continue; }
        let inp = format!("{} {}\n", a, b);
        let (fw, d, sw) = Solution::dice_outcomes(a, b);
        let outs = format!("{} {} {}\n", fw, d, sw);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }

    let formats: [fn(i32, i32) -> String; 4] = [
        |a, b| format!("{}  {}\n", a, b),
        |a, b| format!("{}\t{}\n", a, b),
        |a, b| format!("{} {}\n\n", a, b),
        |a, b| format!(" {} {} \n", a, b),
    ];
    'outer: for fmt in &formats {
        for &(a, b) in &pairs {
            if count >= 100 { break 'outer; }
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

