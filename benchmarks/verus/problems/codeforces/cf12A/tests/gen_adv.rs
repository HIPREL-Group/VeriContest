use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: u32) -> (result: Vec<u8>)
    requires
        seed < 512,
    ensures
        result.len() == 9,
        forall|i: int| 0 <= i < 9 ==> (#[trigger] result[i] == 0u8 || result[i] == 1u8),
{
    let mut grid: Vec<u8> = Vec::new();
    let mut i: u32 = 0;
    while i < 9
        invariant
            grid.len() == i,
            forall|j: int| 0 <= j < i ==> (#[trigger] grid[j] == 0u8 || grid[j] == 1u8),
            i <= 9,
        decreases 9 - i,
    {
        let bit_u32: u32 = (seed >> i) & 1u32;
        let bit: u8 = if bit_u32 == 0 { 0u8 } else { 1u8 };
        grid.push(bit);
        i += 1;
    }
    grid
}

}

use std::io::Write;
use std::collections::HashSet;

struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0
    }
}

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
    let target: usize = 200;
    let mut rng = Rng::new(12);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut seen: HashSet<String> = HashSet::new();
    let mut count = 0usize;

    let mut emit = |inp: String, g: Vec<u8>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if !seen.insert(inp.clone()) { return; }
        let ans = Solution::is_symmetric(g);
        let outp = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    for s in 0..512u32 {
        let g = generate_test_case(s);
        let inp = build_input(&g);
        emit(inp, g, &mut seen, &mut out, &mut count);
        if count >= target { break; }
    }
    let edge = [0u32, 1, 256, 257, 511, 16, 273];
    for &s in &edge {
        let g = generate_test_case(s);
        // Add trailing whitespace variants
        let mut s_clean = build_input(&g);
        emit(format!("{}", s_clean.trim_end()), g.clone(), &mut seen, &mut out, &mut count);
        s_clean.push('\n');
        emit(s_clean, g, &mut seen, &mut out, &mut count);
    }
    while count < target {
        let s = (rng.next_u64() % 512) as u32;
        let g = generate_test_case(s);
        let inp = build_input(&g);
        emit(inp, g, &mut seen, &mut out, &mut count);
    }
}
