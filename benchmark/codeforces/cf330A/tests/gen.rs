use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    r: usize,
    c: usize,
    raw_grid: Vec<Vec<u8>>,
    mutation_kind: u8,
) -> (result: (usize, usize, Vec<Vec<u8>>))
    requires
        2 <= r <= 10,
        2 <= c <= 10,
        raw_grid.len() == r,
        forall|i: int| 0 <= i < raw_grid.len() ==> #[trigger] raw_grid[i].len() == c,
        forall|i: int, j: int| 0 <= i < raw_grid.len() && 0 <= j < raw_grid[i].len() ==> #[trigger] raw_grid[i][j] == 0u8 || raw_grid[i][j] == 1u8,
    ensures
        2 <= result.0 <= 10,
        2 <= result.1 <= 10,
        result.2.len() == result.0,
        forall|i: int| 0 <= i < result.2.len() ==> #[trigger] result.2[i].len() == result.1,
        forall|i: int, j: int| 0 <= i < result.2.len() && 0 <= j < result.2[i].len() ==> #[trigger] result.2[i][j] == 0u8 || result.2[i][j] == 1u8,
{
    if mutation_kind == 0 {
        (r, c, raw_grid)
    } else {
        (r, c, raw_grid)
    }
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

fn build_input(r: usize, c: usize, grid: &[Vec<u8>]) -> String {
    let mut s = format!("{} {}\n", r, c);
    for row in grid {
        for &b in row {
            s.push(if b == 1 { 'S' } else { '.' });
        }
        s.push('\n');
    }
    s
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(330);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |r: usize, c: usize, grid: &Vec<Vec<u8>>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if r < 2 || r > 10 || c < 2 || c > 10 || grid.len() != r { return; }
        if grid.iter().any(|row| row.len() != c) { return; }
        let inp = build_input(r, c, grid);
        if !seen.insert(inp.clone()) { return; }
        let result = Solution::cakeminator(r, c, grid.clone());
        let outp = format!("{}\n", result);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    // Example
    emit(3, 4, &vec![vec![1,0,0,0], vec![0,0,0,0], vec![0,0,1,0]], &mut seen, &mut out, &mut count);

    // All zeros
    emit(2, 2, &vec![vec![0,0], vec![0,0]], &mut seen, &mut out, &mut count);
    emit(10, 10, &(0..10).map(|_| vec![0u8; 10]).collect::<Vec<_>>(), &mut seen, &mut out, &mut count);

    // All ones
    emit(2, 2, &vec![vec![1,1], vec![1,1]], &mut seen, &mut out, &mut count);

    // Random
    while count < target {
        let r = rng.gen_range_usize(2, 10);
        let c = rng.gen_range_usize(2, 10);
        let grid: Vec<Vec<u8>> = (0..r).map(|_| (0..c).map(|_| (rng.next_u64() % 3 == 0) as u8).collect()).collect();
        emit(r, c, &grid, &mut seen, &mut out, &mut count);
    }
}
