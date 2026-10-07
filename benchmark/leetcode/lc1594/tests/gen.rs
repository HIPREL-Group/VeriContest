use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    m: usize,
    n: usize,
    vals: &Vec<i32>,
    mutation_kind: u8,
) -> (result: Vec<Vec<i32>>)
    requires
        1 <= m <= 15,
        1 <= n <= 15,
        vals.len() == m * n,
        forall|k: int| 0 <= k < vals.len() ==> -4 <= #[trigger] vals[k] <= 4,
    ensures
        1 <= result.len() <= 15,
        1 <= result[0].len() <= 15,
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i].len() == result[0].len(),
        forall|i: int, j: int|
            0 <= i < result.len() && 0 <= j < result[i].len()
                ==> -4 <= #[trigger] result[i][j] <= 4,
{
    let mut grid: Vec<Vec<i32>> = Vec::new();
    let mut idx: usize = 0;
    let mut i: usize = 0;
    while i < m
        invariant
            0 <= i <= m,
            1 <= m <= 15,
            1 <= n <= 15,
            vals.len() == m * n,
            idx == i * n,
            idx <= vals.len(),
            grid.len() == i as nat,
            forall|k: int| 0 <= k < vals.len() ==> -4 <= #[trigger] vals[k] <= 4,
            forall|r: int| 0 <= r < i as int ==> (#[trigger] grid[r]).len() == n,
            forall|r: int, c: int|
                0 <= r < i as int && 0 <= c < n as int
                    ==> -4 <= #[trigger] grid[r][c] <= 4,
        decreases m - i,
    {
        let mut row: Vec<i32> = Vec::new();
        let row_start = idx;
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= i < m,
                0 <= j <= n,
                1 <= m <= 15,
                1 <= n <= 15,
                vals.len() == m * n,
                row_start == i * n,
                idx == row_start + j,
                idx <= vals.len(),
                row.len() == j as nat,
                forall|k: int| 0 <= k < vals.len() ==> -4 <= #[trigger] vals[k] <= 4,
                forall|c: int| 0 <= c < j as int ==> -4 <= #[trigger] row[c] <= 4,
            decreases n - j,
        {
            assert(idx < vals.len()) by {
                assert(idx == i * n + j);
                assert(i * n + j < m * n) by (nonlinear_arith)
                    requires 0 <= i, i < m, 0 <= j, j < n
                {}
            }
            let v = if mutation_kind == 1 {
                0i32
            } else if mutation_kind == 2 {
                if vals[idx] > -4 && vals[idx] < 4 {
                    vals[idx]
                } else {
                    0i32
                }
            } else {
                vals[idx]
            };
            row.push(v);
            idx = idx + 1;
            j += 1;
        }
        grid.push(row);
        assert(idx == (i + 1) * n) by (nonlinear_arith)
            requires idx == i * n + n
        {}
        i += 1;
    }
    grid
}

} // verus!

extern crate serde_json;
use serde_json::json;

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0
    }
    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let (lo, hi) = if lo <= hi { (lo, hi) } else { (hi, lo) };
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let (lo, hi) = if lo <= hi { (lo, hi) } else { (hi, lo) };
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

struct Solution;
include!("../code.rs");

fn random_vals(rng: &mut Rng, count: usize) -> Vec<i32> {
    let mut vals = Vec::with_capacity(count);
    for _ in 0..count {
        vals.push(rng.gen_range_i64(-4, 4) as i32);
    }
    vals
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1594);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |grid: Vec<Vec<i32>>,
                    seen: &mut HashSet<String>,
                    out: &mut std::io::BufWriter<std::fs::File>,
                    count: &mut usize| {
        if *count >= target_count { return; }
        let key = format!("{:?}", grid);
        if !seen.insert(key) { return; }
        let output = Solution::max_product_path(grid.clone());
        writeln!(out, "{}", json!({
            "input": {"grid": grid},
            "output": output
        })).unwrap();
        *count += 1;
    };

    // Example test cases from description.md
    let examples: Vec<Vec<Vec<i32>>> = vec![
        vec![vec![-1,-2,-3], vec![-2,-3,-3], vec![-3,-3,-2]],
        vec![vec![1,-2,1], vec![1,-2,1], vec![3,-4,1]],
        vec![vec![1,3], vec![0,-4]],
    ];
    for ex in examples {
        emit(ex, &mut seen, &mut out, &mut count);
    }

    // Boundary / special seed grids with mutations
    let special_configs: Vec<(usize, usize, Vec<i32>)> = vec![
        (1, 1, vec![0]),
        (1, 1, vec![4]),
        (1, 1, vec![-4]),
        (1, 1, vec![1]),
        (2, 2, vec![1, 1, 1, 1]),
        (2, 2, vec![-1, -1, -1, -1]),
        (2, 2, vec![0, 0, 0, 0]),
        (2, 2, vec![4, 4, 4, 4]),
        (2, 2, vec![-4, -4, -4, -4]),
        (1, 15, vec![4; 15]),
        (15, 1, vec![-4; 15]),
        (3, 3, vec![1, -1, 1, -1, 1, -1, 1, -1, 1]),
        (3, 3, vec![0, 1, 2, 3, 4, -1, -2, -3, -4]),
    ];
    let mutation_kinds: Vec<u8> = vec![0, 1, 2];

    for (m, n, vals) in &special_configs {
        for &mk in &mutation_kinds {
            if count >= target_count { break; }
            let grid = generate_test_case(*m, *n, vals, mk);
            emit(grid, &mut seen, &mut out, &mut count);
        }
    }

    // Random grids across size classes
    let mut _attempts_0 = 0usize;
    while count < target_count {
        _attempts_0 += 1; if _attempts_0 > 10000 { break; }
        let (m, n) = match count % 6 {
            0 => (1, 1),
            1 => (rng.gen_range_usize(1, 3), rng.gen_range_usize(1, 3)),
            2 => (rng.gen_range_usize(2, 5), rng.gen_range_usize(2, 5)),
            3 => (rng.gen_range_usize(4, 8), rng.gen_range_usize(4, 8)),
            4 => (rng.gen_range_usize(8, 12), rng.gen_range_usize(8, 12)),
            _ => (rng.gen_range_usize(12, 15), rng.gen_range_usize(12, 15)),
        };
        let vals = random_vals(&mut rng, m * n);
        let mk = rng.gen_range_usize(0, 2) as u8;
        let grid = generate_test_case(m, n, &vals, mk);
        emit(grid, &mut seen, &mut out, &mut count);
    }
}
