use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: usize, m: usize) -> (result: (Vec<Vec<u8>>, usize, usize))
    requires
        1 <= n <= 50,
        1 <= m <= 50,
    ensures
        1 <= result.1 <= 50,
        1 <= result.2 <= 50,
        result.0.len() == result.1,
        forall|i: int| 0 <= i < result.0.len() ==> #[trigger] result.0[i].len() == result.2,
        forall|i: int, j: int| 0 <= i < result.0.len() && 0 <= j < result.0[i].len()
            ==> #[trigger] result.0[i][j] == 0u8 || result.0[i][j] == 1u8,
        exists|i: int, j: int| 0 <= i < result.1 && 0 <= j < result.2 && #[trigger] result.0[i][j] == 1u8,
{
    let mut grid: Vec<Vec<u8>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            1 <= n <= 50,
            1 <= m <= 50,
            grid.len() == i,
            forall|a: int| 0 <= a < grid.len() ==> #[trigger] grid[a].len() == m,
            forall|a: int, b: int| 0 <= a < grid.len() && 0 <= b < grid[a].len()
                ==> #[trigger] grid[a][b] == 0u8 || grid[a][b] == 1u8,
            i > 0 ==> grid[0int][0int] == 1u8,
        decreases n - i,
    {
        let mut row: Vec<u8> = Vec::new();
        let mut j: usize = 0;
        while j < m
            invariant
                0 <= j <= m,
                1 <= m <= 50,
                row.len() == j,
                i == 0 && j > 0 ==> row[0int] == 1u8,
                i > 0 ==> forall|b: int| 0 <= b < row.len() ==> #[trigger] row[b] == 0u8,
                i == 0 ==> forall|b: int| 1 <= b < row.len() ==> #[trigger] row[b] == 0u8,
            decreases m - j,
        {
            if i == 0 && j == 0 {
                row.push(1u8);
            } else {
                row.push(0u8);
            }
            j += 1;
        }
        grid.push(row);
        i += 1;
    }
    proof {
        assert(grid[0int][0int] == 1u8);
        assert(0 <= 0int && 0int < n as int);
        assert(0 <= 0int && 0int < m as int);
    }
    (grid, n, m)
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

fn build_case(n: usize, m: usize, raw: &Vec<Vec<u8>>) -> (String, String) {
    let mut inp = format!("{} {}\n", n, m);
    for row in raw {
        for &b in row {
            inp.push(b as char);
        }
        inp.push('\n');
    }
    let grid: Vec<Vec<u8>> = raw.iter().map(|r| r.iter().map(|&b| if b == b'*' { 1u8 } else { 0u8 }).collect()).collect();
    let (min_r, max_r, min_c, max_c) = Solution::bounding_box(&grid, n, m);
    let mut outp = String::new();
    for r in min_r..=max_r {
        for c in min_c..=max_c {
            outp.push(raw[r][c] as char);
        }
        outp.push('\n');
    }
    (inp, outp)
}

fn rand_grid(rng: &mut Rng, n: usize, m: usize, prob_star: u32) -> Vec<Vec<u8>> {
    loop {
        let mut grid: Vec<Vec<u8>> = Vec::with_capacity(n);
        let mut has_star = false;
        for _ in 0..n {
            let mut row: Vec<u8> = Vec::with_capacity(m);
            for _ in 0..m {
                if ((rng.next_u64() % 100) as u32) < prob_star {
                    row.push(b'*');
                    has_star = true;
                } else {
                    row.push(b'.');
                }
            }
            grid.push(row);
        }
        if has_star { return grid; }
    }
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(0x14AA);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut tries = 0;
    while count < target && tries < target * 200 {
        tries += 1;
        let n = match rng.next_u64() % 4 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(1, 15),
            2 => rng.gen_range_usize(1, 30),
            _ => rng.gen_range_usize(1, 50),
        };
        let m = match rng.next_u64() % 4 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(1, 15),
            2 => rng.gen_range_usize(1, 30),
            _ => rng.gen_range_usize(1, 50),
        };
        let prob = match rng.next_u64() % 5 {
            0 => 10,
            1 => 30,
            2 => 50,
            3 => 70,
            _ => 90,
        };
        let g = rand_grid(&mut rng, n, m, prob);
        let (inp, outp) = build_case(n, m, &g);
        if !seen.insert(inp.clone()) { continue; }
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}
