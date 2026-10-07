use vstd::prelude::*;

verus! {

// Spec fn helper copied from spec.rs
pub open spec fn is_mark(grid: Seq<Vec<i32>>, i: int, j: int) -> bool
    recommends
        0 <= i < grid.len(),
        0 <= j < grid[0].len(),
{
    grid[i][j] == 1
}

/// Build an n×m grid of 0/1 values with at least one marked cell.
///
/// Construction parameters:
///   n, m        — grid dimensions
///   mark_r, mark_c — guaranteed mark position
///   mutation_kind  — selects how many additional marks to place
///
/// mutation_kind variants:
///   0 — single mark at (mark_r, mark_c)
///   1 — entire grid filled with 1s
///   2 — entire row mark_r filled with 1s
///   3 — entire column mark_c filled with 1s
///   _ — fallback: single mark
pub fn generate_test_case(
    n: usize,
    m: usize,
    mark_r: usize,
    mark_c: usize,
    mutation_kind: u8,
) -> (result: Vec<Vec<i32>>)
    requires
        1 <= n <= 1000,
        1 <= m <= 1000,
        mark_r < n,
        mark_c < m,
    ensures
        0 < result.len(),
        0 < result[0].len(),
        result.len() <= 200000,
        result[0].len() <= 200000,
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i].len() == result[0].len(),
        forall|i: int, j: int|
            0 <= i < result.len() && 0 <= j < result[0].len() ==> (#[trigger] result[i][j] == 0 || #[trigger] result[i][j] == 1),
        exists|i: int, j: int| 0 <= i < result.len() && 0 <= j < result[0].len() && #[trigger] is_mark(result@, i, j),
{
    let mut grid: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            1 <= n <= 1000,
            1 <= m <= 1000,
            mark_r < n,
            mark_c < m,
            grid.len() == i as int,
            forall|r: int| 0 <= r < i as int ==> (#[trigger] grid[r]).len() == m,
            forall|r: int, c: int|
                0 <= r < i as int && 0 <= c < m as int
                ==> (#[trigger] grid[r][c] == 0 || #[trigger] grid[r][c] == 1),
            // Track that the mark is placed when we've passed mark_r
            (mark_r < i) ==> grid[mark_r as int][mark_c as int] == 1i32,
        decreases n - i,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < m
            invariant
                j <= m,
                1 <= m <= 1000,
                mark_c < m,
                row.len() == j as int,
                forall|c: int| 0 <= c < j as int
                    ==> (#[trigger] row[c] == 0 || #[trigger] row[c] == 1),
                // Track the mark in the current row
                (i == mark_r && mark_c < j) ==> row[mark_c as int] == 1i32,
            decreases m - j,
        {
            let val: i32 = if i == mark_r && j == mark_c {
                1  // always mark the designated position
            } else if mutation_kind == 1 {
                1  // all 1s
            } else if mutation_kind == 2 && i == mark_r {
                1  // full row of marks
            } else if mutation_kind == 3 && j == mark_c {
                1  // full column of marks
            } else {
                0
            };
            row.push(val);
            j += 1;
        }
        grid.push(row);
        i += 1;
    }

    proof {
        assert(grid@[mark_r as int][mark_c as int] == 1i32);
        assert(is_mark(grid@, mark_r as int, mark_c as int));
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
        self.0 = self.0.wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
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

fn build_circle(n: usize, m: usize, ch: usize, ck: usize, r: usize) -> Vec<Vec<i32>> {
    // Builds a manhattan circle: cells (i,j) with |i-ch| + |j-ck| < r
    let mut grid = vec![vec![0i32; m]; n];
    for i in 0..n {
        for j in 0..m {
            let di = if i >= ch { i - ch } else { ch - i };
            let dj = if j >= ck { j - ck } else { ck - j };
            if di + dj < r {
                grid[i][j] = 1;
            }
        }
    }
    grid
}

fn max_radius(n: usize, m: usize, ch: usize, ck: usize) -> usize {
    let a = ch + 1;
    let b = n - ch;
    let c = ck + 1;
    let d = m - ck;
    a.min(b).min(c).min(d)
}

fn build_input(cases: &[Vec<Vec<i32>>]) -> String {
    let mut s = format!("{}\n", cases.len());
    for grid in cases {
        let n = grid.len();
        let m = grid[0].len();
        s.push_str(&format!("{} {}\n", n, m));
        for row in grid {
            let mut rs = String::with_capacity(m);
            for &v in row {
                rs.push(if v == 1 { '#' } else { '.' });
            }
            rs.push('\n');
            s.push_str(&rs);
        }
    }
    s
}

fn build_output(answers: &[(i32, i32)]) -> String {
    let mut s = String::new();
    for &(r, c) in answers {
        s.push_str(&format!("{} {}\n", r, c));
    }
    s
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut count = 0usize;

    // Examples from description
    let examples: Vec<Vec<Vec<i32>>> = vec![
        vec![
            vec![0,0,0,0,0],
            vec![0,0,1,0,0],
            vec![0,1,1,1,0],
            vec![0,0,1,0,0],
            vec![0,0,0,0,0],
        ],
        vec![
            vec![0,0,1,0,0],
            vec![0,1,1,1,0],
            vec![1,1,1,1,1],
            vec![0,1,1,1,0],
            vec![0,0,1,0,0],
        ],
        vec![
            vec![0,0,0,0,0,0],
            vec![0,0,0,0,0,0],
            vec![0,0,1,0,0,0],
            vec![0,1,1,1,0,0],
            vec![0,0,1,0,0,0],
        ],
        vec![vec![1]],
        vec![
            vec![0,0,0,1,0,0],
            vec![0,0,1,1,1,0],
            vec![0,1,1,1,1,1],
            vec![0,0,1,1,1,0],
            vec![0,0,0,1,0,0],
        ],
        vec![
            vec![0,0,0,0,0,0,1,0,0,0],
            vec![0,0,0,0,0,1,1,1,0,0],
        ],
    ];
    let cases_one = vec![examples.clone()];
    {
        // Emit example as a single bundle
        let answers: Vec<(i32, i32)> = examples.iter().map(|g| Solution::manhattan_circle_center(g.clone())).collect();
        let inp = build_input(&examples);
        let outp = build_output(&answers);
        let key = format!("{:?}", examples);
        if seen.insert(key) {
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
            count += 1;
        }
    }
    let _ = cases_one;

    while count < target {
        let t: usize = if count < 5 { 1 }
                       else if count < 30 { rng.gen_range_usize(2, 5) }
                       else if count < 60 { rng.gen_range_usize(3, 10) }
                       else { rng.gen_range_usize(5, 20) };

        let mut cases: Vec<Vec<Vec<i32>>> = Vec::new();
        let mut total = 0usize;
        for _ in 0..t {
            let n = rng.gen_range_usize(1, 20);
            let m = rng.gen_range_usize(1, 20);
            if total + n * m > 5000 { break; }
            let ch = rng.gen_range_usize(0, n - 1);
            let ck = rng.gen_range_usize(0, m - 1);
            let mr = max_radius(n, m, ch, ck);
            let r = rng.gen_range_usize(1, mr);
            let grid = build_circle(n, m, ch, ck, r);
            total += n * m;
            cases.push(grid);
        }
        if cases.is_empty() { continue; }
        let key = format!("{:?}", cases);
        if !seen.insert(key) { continue; }
        let answers: Vec<(i32, i32)> = cases.iter().map(|g| Solution::manhattan_circle_center(g.clone())).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

