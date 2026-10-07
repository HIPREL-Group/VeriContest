use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    raw_grid: Vec<u8>,
) -> (result: Vec<u8>)
    requires
        raw_grid.len() == 64,
        forall|i: int| 0 <= i < 64 ==> #[trigger] raw_grid[i] <= 2,
    ensures
        result.len() == 64,
        forall|i: int| 0 <= i < 64 ==> #[trigger] result[i] <= 2,
{
    raw_grid
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

fn grid_to_string(grid: &Vec<u8>) -> String {
    let mut s = String::new();
    for r in 0..8 {
        for c in 0..8 {
            let ch = match grid[r * 8 + c] {
                0 => 'R',
                1 => 'B',
                _ => '.',
            };
            s.push(ch);
        }
        s.push('\n');
    }
    s
}

fn build_input(cases: &[Vec<u8>]) -> String {
    let mut s = format!("{}\n", cases.len());
    for g in cases {
        s.push_str(&grid_to_string(g));
    }
    s
}

fn build_output(cases: &[Vec<u8>]) -> String {
    let mut s = String::new();
    for g in cases {
        let r = Solution::red_last(g.clone());
        s.push_str(if r { "R\n" } else { "B\n" });
    }
    s
}

fn random_valid_grid(rng: &mut Rng) -> Vec<u8> {
    // Pick which rows are red and which columns are blue, then their order.
    let mut grid: Vec<u8> = vec![2u8; 64];
    let mut steps: Vec<(u8, usize)> = Vec::new();  // 0=R-row, 1=B-col
    let prob = (rng.next_u64() % 7) + 1;  // randomize probability
    for r in 0..8 {
        if rng.next_u64() % prob == 0 {
            steps.push((0, r));
        }
    }
    for c in 0..8 {
        if rng.next_u64() % prob == 0 {
            steps.push((1, c));
        }
    }
    if steps.is_empty() {
        if rng.next_u64() % 2 == 0 {
            steps.push((0, (rng.next_u64() as usize) % 8));
        } else {
            steps.push((1, (rng.next_u64() as usize) % 8));
        }
    }
    let n = steps.len();
    for i in 0..n {
        let j = (rng.next_u64() as usize) % n;
        steps.swap(i, j);
    }
    for (typ, idx) in steps {
        if typ == 0 {
            for c in 0..8 {
                grid[idx * 8 + c] = 0;
            }
        } else {
            for r in 0..8 {
                grid[r * 8 + idx] = 1;
            }
        }
    }
    grid
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(1742);
    let mut seen: HashSet<String> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);

    // Sample
    {
        let s1 = "....B...\n....B...\n....B...\nRRRRRRRR\n....B...\n....B...\n....B...\n....B...\n";
        let s2 = "RRRRRRRB\nB......B\nB......B\nB......B\nB......B\nB......B\nB......B\nRRRRRRRB\n";
        let s3 = "RRRRRRBB\n.B.B..BB\nRRRRRRBB\n.B.B..BB\n.B.B..BB\nRRRRRRBB\n.B.B..BB\n.B.B..BB\n";
        let s4 = "........\n........\n........\nRRRRRRRR\n........\n........\n........\n........\n";
        fn parse_grid(s: &str) -> Vec<u8> {
            let mut grid = Vec::with_capacity(64);
            for ch in s.chars() {
                if ch == '\n' { continue; }
                grid.push(match ch { 'R' => 0u8, 'B' => 1u8, _ => 2u8 });
            }
            grid
        }
        let cases: Vec<Vec<u8>> = vec![parse_grid(s1), parse_grid(s2), parse_grid(s3), parse_grid(s4)];
        let inp = build_input(&cases);
        if seen.insert(inp.clone()) {
            let outp = build_output(&cases);
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        }
    }

    let mut count = 1usize;
    let mut tries = 0;
    while count < target && tries < target * 100 {
        tries += 1;
        let t = rng.gen_range_usize(1, 5);
        let mut cases: Vec<Vec<u8>> = Vec::new();
        for _ in 0..t {
            cases.push(random_valid_grid(&mut rng));
        }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let outp = build_output(&cases);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}
