use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: usize, bits: &Vec<i32>) -> (result: (Vec<i32>, usize))
    requires
        1 <= n <= 1000,
        bits.len() == 3 * n,
        forall|i: int| 0 <= i < bits.len() ==> (#[trigger] bits[i] == 0 || bits[i] == 1),
    ensures
        result.1 == n,
        1 <= result.1 <= 1000,
        result.0.len() == 3 * result.1,
        forall|i: int| 0 <= i < result.0.len() ==> (#[trigger] result.0[i] == 0 || result.0[i] == 1),
{
    let mut grid: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < bits.len()
        invariant
            0 <= i <= bits.len(),
            grid.len() == i,
            bits.len() == 3 * n,
            forall|k: int| 0 <= k < i as int ==> (#[trigger] grid[k] == bits[k]),
            forall|k: int| 0 <= k < bits.len() ==> (#[trigger] bits[k] == 0 || bits[k] == 1),
        decreases bits.len() - i,
    {
        grid.push(bits[i]);
        i = i + 1;
    }
    assert(grid.len() == 3 * n);
    assert forall|k: int| 0 <= k < grid.len() implies (#[trigger] grid[k] == 0 || grid[k] == 1) by {
        assert(grid[k] == bits[k]);
    }
    (grid, n)
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

fn build_input(grid: &[i32], n: usize) -> String {
    let mut s = format!("{}\n", n);
    for i in 0..n {
        s.push_str(&format!("{} {} {}\n", grid[3*i], grid[3*i+1], grid[3*i+2]));
    }
    s
}

fn build_output(ans: usize) -> String {
    format!("{}\n", ans)
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(0x231A);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut tries = 0;
    while count < target && tries < target * 100 {
        tries += 1;
        let n = match tries % 6 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(5, 20),
            2 => rng.gen_range_usize(20, 100),
            3 => rng.gen_range_usize(100, 300),
            4 => rng.gen_range_usize(300, 700),
            _ => rng.gen_range_usize(700, 1000),
        };
        let pat = rng.next_u64() % 4;
        let grid: Vec<i32> = (0..3*n).map(|_| match pat {
            0 => (rng.next_u64() % 2) as i32,
            1 => if rng.next_u64() % 4 == 0 { 1 } else { 0 },
            2 => if rng.next_u64() % 4 != 0 { 1 } else { 0 },
            _ => (rng.next_u64() % 2) as i32,
        }).collect();
        let inp = build_input(&grid, n);
        if !seen.insert(inp.clone()) { continue; }
        let ans = Solution::count_teams_implement(grid, n);
        let outp = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

