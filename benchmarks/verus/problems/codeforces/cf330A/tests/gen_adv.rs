use vstd::prelude::*;

verus! {

pub fn generate_test_case(r: usize, c: usize, grid: Vec<Vec<u8>>) -> (res: (usize, usize, Vec<Vec<u8>>))
    requires
        2 <= r <= 10,
        2 <= c <= 10,
        grid.len() == r,
        forall|i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == c,
        forall|i: int, j: int| 0 <= i < grid.len() && 0 <= j < grid[i].len() ==> #[trigger] grid[i][j] == 0u8 || grid[i][j] == 1u8,
    ensures
        2 <= res.0 <= 10,
        2 <= res.1 <= 10,
        res.2.len() == res.0,
        forall|i: int| 0 <= i < res.2.len() ==> #[trigger] res.2[i].len() == res.1,
        forall|i: int, j: int| 0 <= i < res.2.len() && 0 <= j < res.2[i].len() ==> #[trigger] res.2[i][j] == 0u8 || res.2[i][j] == 1u8,
{
    (r, c, grid)
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
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        lo + (self.next_u64() as usize) % (hi - lo + 1)
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

fn build_input(r: usize, c: usize, grid: &[Vec<u8>], rsep: &str, end: &str) -> String {
    let mut s = format!("{} {}{}", r, c, rsep);
    for row in grid {
        for &b in row {
            s.push(if b == 1 { 'S' } else { '.' });
        }
        s.push_str(rsep);
    }
    s.push_str(end);
    s
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(3301);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |inp: String, r: usize, c: usize, grid: &Vec<Vec<u8>>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if !seen.insert(inp.clone()) { return; }
        let result = Solution::cakeminator(r, c, grid.clone());
        let outp = format!("{}\n", result);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    while count < target {
        let r = rng.gen_range_usize(2, 10);
        let c = rng.gen_range_usize(2, 10);
        let grid: Vec<Vec<u8>> = (0..r).map(|_| (0..c).map(|_| (rng.next_u64() % 3 == 0) as u8).collect()).collect();
        let mode = (rng.next_u64() % 4) as usize;
        let inp = match mode {
            0 => build_input(r, c, &grid, "\n", ""),
            1 => build_input(r, c, &grid, "\r\n", ""),
            2 => build_input(r, c, &grid, "\n", "\n"),
            _ => build_input(r, c, &grid, "\n", " "),
        };
        emit(inp, r, c, &grid, &mut seen, &mut out, &mut count);
    }
}
