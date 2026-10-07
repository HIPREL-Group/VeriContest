use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: u32, mutation_kind: u8) -> (result: Vec<u8>)
    requires
        seed < 512,
    ensures
        result.len() == 9,
        forall|i: int| 0 <= i < 9 ==> (#[trigger] result[i] == 0u8 || result[i] == 1u8),
{
    let mut grid: Vec<u8> = Vec::new();
    let s = if mutation_kind == 0 {
        seed
    } else if mutation_kind == 1 {
        (seed * 3) % 512
    } else if mutation_kind == 2 {
        (seed * 7 + 11) % 512
    } else {
        seed % 512
    };
    let mut i: u32 = 0;
    while i < 9
        invariant
            grid.len() == i,
            forall|j: int| 0 <= j < i ==> (#[trigger] grid[j] == 0u8 || grid[j] == 1u8),
            i <= 9,
        decreases 9 - i,
    {
        let bit_u32: u32 = (s >> i) & 1u32;
        let bit: u8 = if bit_u32 == 0 { 0u8 } else { 1u8 };
        grid.push(bit);
        i += 1;
    }
    grid
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

fn build_input(grid: &[u8]) -> String {
    let mut s = String::new();
    for row in 0..3 {
        for col in 0..3 {
            let v = grid[row * 3 + col];
            if v == 1 { s.push('X'); } else { s.push('.'); }
        }
        s.push('\n');
    }
    s
}

fn build_output(yes: bool) -> String {
    if yes { "YES\n".to_string() } else { "NO\n".to_string() }
}

fn main() {
    let target: usize = 100;
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut seen: HashSet<u32> = HashSet::new();
    let mut count = 0usize;

    let mut emit = |s: u32, mk: u8, seen: &mut HashSet<u32>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        let g = generate_test_case(s, mk);
        let mut key: u32 = 0;
        for k in 0..9 { key |= (g[k] as u32) << k; }
        if !seen.insert(key) { return; }
        let inp = build_input(&g);
        let ans = Solution::is_symmetric(g);
        let outp = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    for s in 0..512u32 {
        emit(s, 0, &mut seen, &mut out, &mut count);
        if count >= target { break; }
    }
    let mut s: u32 = 0;
    while count < target {
        emit(s, 1, &mut seen, &mut out, &mut count);
        emit(s, 2, &mut seen, &mut out, &mut count);
        s = (s + 1) % 512;
    }
}
