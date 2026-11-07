use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: usize, bits: Vec<i32>, mutation_kind: u8) -> (result: (Vec<i32>, usize))
    requires
        1 <= n <= 1000,
        bits.len() == 3 * n,
        forall|i: int| 0 <= i < bits.len() ==> (#[trigger] bits[i] == 0 || bits[i] == 1),
    ensures
        1 <= result.1 <= 1000,
        result.0.len() == 3 * result.1,
        forall|i: int| 0 <= i < result.0.len() ==> (#[trigger] result.0[i] == 0 || result.0[i] == 1),
{
    if mutation_kind == 0 {
        // identity
        (bits, n)
    } else if mutation_kind == 1 {
        // set all elements to 1
        let mut grid = bits;
        let len = 3 * n;
        let mut i: usize = 0;
        while i < len
            invariant
                len == 3 * n,
                1 <= n <= 1000,
                grid.len() == len,
                0 <= i <= len,
                forall|j: int| 0 <= j < i ==> (#[trigger] grid[j] == 1),
                forall|j: int| i <= j < len ==> (#[trigger] grid[j] == 0 || grid[j] == 1),
            decreases len - i,
        {
            grid.set(i, 1);
            i += 1;
        }
        assert forall|j: int| 0 <= j < grid.len() implies (#[trigger] grid[j] == 0 || grid[j] == 1) by {
            // all elements are 1
        }
        (grid, n)
    } else if mutation_kind == 2 {
        // set all elements to 0
        let mut grid = bits;
        let len = 3 * n;
        let mut i: usize = 0;
        while i < len
            invariant
                len == 3 * n,
                1 <= n <= 1000,
                grid.len() == len,
                0 <= i <= len,
                forall|j: int| 0 <= j < i ==> (#[trigger] grid[j] == 0),
                forall|j: int| i <= j < len ==> (#[trigger] grid[j] == 0 || grid[j] == 1),
            decreases len - i,
        {
            grid.set(i, 0);
            i += 1;
        }
        assert forall|j: int| 0 <= j < grid.len() implies (#[trigger] grid[j] == 0 || grid[j] == 1) by {
        }
        (grid, n)
    } else if mutation_kind == 3 && bits.len() >= 1 {
        // flip first element
        let mut grid = bits;
        let old = grid[0];
        if old == 0 {
            grid.set(0, 1);
        } else {
            grid.set(0, 0);
        }
        assert forall|j: int| 0 <= j < grid.len() implies (#[trigger] grid[j] == 0 || grid[j] == 1) by {
            assert(grid[0] == 0 || grid[0] == 1);
        }
        (grid, n)
    } else if mutation_kind == 4 && bits.len() >= 1 {
        // flip last element
        let mut grid = bits;
        let last = grid.len() - 1;
        let old = grid[last];
        if old == 0 {
            grid.set(last, 1);
        } else {
            grid.set(last, 0);
        }
        assert forall|j: int| 0 <= j < grid.len() implies (#[trigger] grid[j] == 0 || grid[j] == 1) by {
        }
        (grid, n)
    } else {
        // fallback: identity
        (bits, n)
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
    let target: usize = 100;
    let mut rng = Rng::new(231);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let examples: Vec<(Vec<i32>, usize)> = vec![
        (vec![1,1,0, 1,1,1, 1,0,0], 3),
        (vec![0,1,0, 1,0,1, 0,1,0, 1,0,0], 4),
    ];
    for (g, n) in &examples {
        if count >= target { break; }
        let inp = build_input(g, *n);
        if !seen.insert(inp.clone()) { continue; }
        let ans = Solution::count_teams_implement(g.clone(), *n);
        let outp = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }

    let mut tries = 0;
    while count < target && tries < target * 100 {
        tries += 1;
        let n = match tries % 6 {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(4, 10),
            2 => rng.gen_range_usize(10, 30),
            3 => rng.gen_range_usize(30, 100),
            4 => rng.gen_range_usize(100, 500),
            _ => rng.gen_range_usize(500, 1000),
        };
        let grid: Vec<i32> = (0..3*n).map(|_| (rng.next_u64() % 2) as i32).collect();
        let inp = build_input(&grid, n);
        if !seen.insert(inp.clone()) { continue; }
        let ans = Solution::count_teams_implement(grid, n);
        let outp = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

