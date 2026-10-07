use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    m: usize,
    ch: usize,  // center row (0-indexed)
    ck: usize,  // center col (0-indexed)
    r: usize,   // radius
) -> (grid: Vec<Vec<i32>>)
    requires
        1 <= n <= 400,
        1 <= m <= 400,
        n * m <= 200000,
        ch < n,
        ck < m,
        r >= 1,
        r <= ch + 1,
        r + ch <= n,
        r <= ck + 1,
        r + ck <= m,
    ensures
        0 < grid.len(),
        0 < grid[0].len(),
        grid.len() == n,
        grid[0].len() == m,
        grid.len() <= 200000,
        grid[0].len() <= 200000,
        forall|i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == grid[0].len(),
        forall|i: int, j: int|
            0 <= i < grid.len() && 0 <= j < grid[0].len()
                ==> (#[trigger] grid[i][j] == 0 || grid[i][j] == 1),
        exists|i: int, j: int| 0 <= i < grid.len() && 0 <= j < grid[0].len() && #[trigger] is_mark(grid@, i, j),
{
    let _ = r;
    let mut grid: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;

    while i < n
        invariant
            0 <= i <= n,
            grid.len() == i,
            1 <= n <= 400,
            1 <= m <= 400,
            ch < n,
            ck < m,
            r >= 1,
            r <= ch + 1,
            r + ch <= n,
            r <= ck + 1,
            r + ck <= m,
            forall|x: int| 0 <= x < i ==> #[trigger] grid[x].len() == m,
            forall|x: int, y: int|
                0 <= x < i && 0 <= y < m
                    ==> (#[trigger] grid[x][y] == 0 || grid[x][y] == 1),
            forall|x: int, y: int|
                0 <= x < i && 0 <= y < m && #[trigger] grid[x][y] == 1
                    ==> x == ch as int && y == ck as int,
            ch < i ==> grid[ch as int][ck as int] == 1,
        decreases n - i,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < m
            invariant
                0 <= j <= m,
                row.len() == j,
                i < n,
                ch < n,
                ck < m,
                r >= 1,
                forall|y: int| 0 <= y < j ==> (#[trigger] row[y] == 0 || row[y] == 1),
                forall|y: int| 0 <= y < j && #[trigger] row[y] == 1
                    ==> i == ch && y == ck as int,
                i == ch && ck < j ==> row[ck as int] == 1,
            decreases m - j,
        {
            let v: i32 = if i == ch && j == ck { 1 } else { 0 };
            row.push(v);
            if i == ch && j == ck {
                assert(row[ck as int] == 1);
            }
            j = j + 1;
        }
        assert(row.len() == m);
        if i == ch {
            assert(ck < row.len());
            assert(row[ck as int] == 1);
        }
        grid.push(row);
        assert(grid[i as int].len() == m);
        if i == ch {
            assert(grid[i as int][ck as int] == 1);
        }
        i = i + 1;
    }

    proof {
        assert(grid.len() == n);
        assert(0 < grid.len());
        assert(0 < grid[0].len());
        assert(grid[0].len() == m);
        assert(grid[ch as int].len() == m);
        assert(grid[ch as int][ck as int] == 1);
        assert(is_mark(grid@, ch as int, ck as int));
        assert(exists|i0: int, j0: int|
            0 <= i0 < grid.len() && 0 <= j0 < grid[0].len() && #[trigger] is_mark(grid@, i0, j0)) by {
            let i0 = ch as int;
            let j0 = ck as int;
            assert(0 <= i0 < grid.len());
            assert(0 <= j0 < grid[0].len());
            assert(is_mark(grid@, i0, j0));
        }
    }

    grid
}

pub open spec fn abs_diff(a: int, b: int) -> int {
    if a >= b { a - b } else { b - a }
}

pub open spec fn is_mark(grid: Seq<Vec<i32>>, i: int, j: int) -> bool {
    grid[i][j] == 1
}

}

use std::io::Write;

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

fn gen_mode(rng: &mut Rng, mode: usize) -> (usize, usize, usize, usize, usize) {
    match mode {
        0 => {
            let n = rng.gen_range_usize(1, 10);
            let m = rng.gen_range_usize(1, 10);
            let ch = rng.gen_range_usize(0, n - 1);
            let ck = rng.gen_range_usize(0, m - 1);
            let mr = max_radius(n, m, ch, ck);
            let r = rng.gen_range_usize(1, mr);
            (n, m, ch, ck, r)
        }
        1 => (1, 1, 0, 0, 1),
        2 => {
            let n = rng.gen_range_usize(3, 20);
            let m = rng.gen_range_usize(3, 20);
            (n, m, 0, 0, 1)
        }
        3 => {
            let n = rng.gen_range_usize(3, 20);
            let m = rng.gen_range_usize(3, 20);
            (n, m, n - 1, m - 1, 1)
        }
        4 => {
            let n = rng.gen_range_usize(5, 15);
            let m = rng.gen_range_usize(5, 15);
            let ch = n / 2;
            let ck = m / 2;
            let mr = max_radius(n, m, ch, ck);
            (n, m, ch, ck, mr)
        }
        5 => {
            let m = rng.gen_range_usize(5, 50);
            let n = 1;
            let ck = rng.gen_range_usize(0, m - 1);
            (n, m, 0, ck, 1)
        }
        6 => {
            let n = rng.gen_range_usize(5, 50);
            let m = 1;
            let ch = rng.gen_range_usize(0, n - 1);
            (n, m, ch, 0, 1)
        }
        7 => {
            let n = rng.gen_range_usize(20, 50);
            let m = rng.gen_range_usize(20, 50);
            let ch = rng.gen_range_usize(0, n - 1);
            let ck = rng.gen_range_usize(0, m - 1);
            let mr = max_radius(n, m, ch, ck);
            let r = rng.gen_range_usize(1, mr);
            (n, m, ch, ck, r)
        }
        8 => {
            let n = rng.gen_range_usize(50, 100);
            let m = rng.gen_range_usize(50, 100);
            let ch = rng.gen_range_usize(0, n - 1);
            let ck = rng.gen_range_usize(0, m - 1);
            let mr = max_radius(n, m, ch, ck);
            let r = rng.gen_range_usize(1, mr);
            (n, m, ch, ck, r)
        }
        9 => {
            let n = rng.gen_range_usize(2, 30);
            let m = rng.gen_range_usize(2, 30);
            let ch = rng.gen_range_usize(0, n - 1);
            let ck = rng.gen_range_usize(0, m - 1);
            (n, m, ch, ck, 1)
        }
        _ => {
            let n = rng.gen_range_usize(1, 20);
            let m = rng.gen_range_usize(1, 20);
            let ch = rng.gen_range_usize(0, n - 1);
            let ck = rng.gen_range_usize(0, m - 1);
            let mr = max_radius(n, m, ch, ck);
            let r = rng.gen_range_usize(1, mr);
            (n, m, ch, ck, r)
        }
    }
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
    let target: usize = 200;
    let mut rng = Rng::new(1);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut count = 0usize;
    let modes = 11usize;

    while count < target {
        let t: usize = if count < 20 { 1 }
                       else if count < 80 { rng.gen_range_usize(2, 6) }
                       else if count < 150 { rng.gen_range_usize(3, 12) }
                       else { rng.gen_range_usize(5, 25) };
        let mut cases: Vec<Vec<Vec<i32>>> = Vec::new();
        let mut total = 0usize;
        for sub in 0..t {
            let mode = (count * 7 + sub) % modes;
            let (n, m, ch, ck, r) = gen_mode(&mut rng, mode);
            if total + n * m > 30000 { break; }
            total += n * m;
            cases.push(build_circle(n, m, ch, ck, r));
        }
        if cases.is_empty() { continue; }
        let answers: Vec<(i32, i32)> = cases.iter().map(|g| Solution::manhattan_circle_center(g.clone())).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

