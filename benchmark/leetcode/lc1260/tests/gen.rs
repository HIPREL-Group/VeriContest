use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    m: usize,
    n: usize,
    values: &Vec<i32>,
    k: i32,
    mutation_kind: u8,
) -> (result: (Vec<Vec<i32>>, i32))
    requires
        1 <= m <= 50,
        1 <= n <= 50,
        values.len() == m * n,
        forall|idx: int| 0 <= idx < values.len() ==> -1000 <= #[trigger] values[idx] <= 1000,
        0 <= k <= 100,
    ensures
        1 <= result.0.deep_view().len() <= 50,
        forall|i: int|
            0 <= i < result.0.deep_view().len() ==> 1 <= (#[trigger] result.0.deep_view()[i]).len()
                <= 50,
        forall|i: int|
            0 <= i < result.0.deep_view().len() ==> (#[trigger] result.0.deep_view()[i]).len()
                == result.0.deep_view()[0].len(),
        forall|i: int, j: int|
            0 <= i < result.0.deep_view().len() && 0 <= j < result.0.deep_view()[i].len() ==> -1000
                <= #[trigger] result.0.deep_view()[i][j] <= 1000,
        0 <= result.1 <= 100,
{
    let mut grid: Vec<Vec<i32>> = Vec::new();
    let mut ri: usize = 0;
    while ri < m
        invariant
            0 <= ri <= m,
            1 <= m <= 50,
            1 <= n <= 50,
            grid.len() == ri as nat,
            values.len() == m * n,
            forall|idx: int| 0 <= idx < values.len() ==> -1000 <= #[trigger] values[idx] <= 1000,
            forall|r: int|
                0 <= r < ri as int ==> (#[trigger] grid.deep_view()[r]).len() == n as int,
            forall|r: int, c: int|
                0 <= r < ri as int && 0 <= c < n as int
                    ==> -1000 <= #[trigger] grid.deep_view()[r][c] <= 1000,
        decreases m - ri,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut cj: usize = 0;
        while cj < n
            invariant
                0 <= cj <= n,
                1 <= n <= 50,
                1 <= m <= 50,
                0 <= ri < m,
                row.len() == cj as nat,
                values.len() == m * n,
                forall|idx: int| 0 <= idx < values.len() ==> -1000 <= #[trigger] values[idx] <= 1000,
                forall|c: int| 0 <= c < cj as int ==> -1000 <= #[trigger] row@[c] <= 1000,
            decreases n - cj,
        {
            assert(ri * n + cj < m * n) by(nonlinear_arith)
                requires ri < m, cj < n, m >= 1, n >= 1;
            row.push(values[ri * n + cj]);
            cj += 1;
        }
        assert(row@.len() == n as int);
        assert(forall|c: int| 0 <= c < n as int ==> -1000 <= #[trigger] row@[c] <= 1000);
        let ghost prev_grid = grid.deep_view();
        grid.push(row);
        assert(grid.deep_view().len() == ri as int + 1);
        proof {
            assert forall|r: int|
                0 <= r < ri as int + 1 implies (#[trigger] grid.deep_view()[r]).len() == n as int
            by {
                if r < ri as int {
                    assert(grid.deep_view()[r] =~= prev_grid[r]);
                }
            }
            assert forall|r: int, c: int|
                0 <= r < ri as int + 1 && 0 <= c < n as int implies
                    -1000 <= #[trigger] grid.deep_view()[r][c] <= 1000
            by {
                if r < ri as int {
                    assert(grid.deep_view()[r] =~= prev_grid[r]);
                }
            }
        }
        ri += 1;
    }

    let k_out: i32 = if mutation_kind == 1 && k < 100 {
        k + 1
    } else if mutation_kind == 2 && k > 0 {
        k - 1
    } else if mutation_kind == 3 {
        0i32
    } else if mutation_kind == 4 {
        100i32
    } else {
        k
    };

    (grid, k_out)
}

} // verus!

extern crate serde_json;
use serde_json::json;

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0
    }
    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

struct Solution;
include!("../code.rs");

fn flatten_grid(grid: &Vec<Vec<i32>>) -> Vec<i32> {
    let mut flat = Vec::new();
    for row in grid {
        for &v in row {
            flat.push(v);
        }
    }
    flat
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1260);
    let count_target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |grid: Vec<Vec<i32>>, k: i32,
                    seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>,
                    count: &mut usize| {
        if *count >= count_target { return; }
        let key = format!("{:?},{}", grid, k);
        if !seen.insert(key) { return; }
        let output = Solution::shift_grid(grid.clone(), k);
        writeln!(out, "{}", json!({
            "input": {"grid": grid, "k": k},
            "output": output
        })).unwrap();
        *count += 1;
    };

    // Example test cases from description.md
    let examples: Vec<(Vec<Vec<i32>>, i32)> = vec![
        (vec![vec![1,2,3], vec![4,5,6], vec![7,8,9]], 1),
        (vec![vec![3,8,1,9], vec![19,7,2,5], vec![4,6,11,10], vec![12,0,21,13]], 4),
        (vec![vec![1,2,3], vec![4,5,6], vec![7,8,9]], 9),
    ];
    for (grid, k) in &examples {
        let m = grid.len();
        let n = grid[0].len();
        let flat = flatten_grid(grid);
        for mk in 0..=4u8 {
            let (g, kk) = generate_test_case(m, n, &flat, *k, mk);
            emit(g, kk, &mut seen, &mut out, &mut count);
        }
    }

    // Special configurations: boundary sizes
    let configs: Vec<(usize, usize)> = vec![
        (1, 1), (1, 2), (2, 1), (1, 50), (50, 1),
        (2, 2), (3, 3), (5, 5), (10, 10), (25, 25), (50, 50),
        (1, 10), (10, 1), (7, 7), (50, 2), (2, 50),
    ];

    let k_values: Vec<i32> = vec![0, 1, 50, 99, 100];

    for &(m, n) in &configs {
        for &k in &k_values {
            if count >= count_target { break; }
            let total = m * n;
            let mut flat: Vec<i32> = Vec::with_capacity(total);
            for idx in 0..total {
                // Sequential values modulated to -1000..1000
                flat.push(((idx as i64 % 2001) - 1000) as i32);
            }
            let mk = (rng.next_u64() % 5) as u8;
            let (g, kk) = generate_test_case(m, n, &flat, k, mk);
            emit(g, kk, &mut seen, &mut out, &mut count);
        }
    }

    // Random test cases with diverse sizes and values
    while count < count_target {
        let m = match count % 5 {
            0 => 1,
            1 => rng.gen_range_usize(1, 5),
            2 => rng.gen_range_usize(5, 15),
            3 => rng.gen_range_usize(15, 35),
            _ => rng.gen_range_usize(35, 50),
        };
        let n = match count % 7 {
            0 => 1,
            1 => rng.gen_range_usize(1, 5),
            2 | 3 => rng.gen_range_usize(5, 15),
            4 | 5 => rng.gen_range_usize(15, 35),
            _ => rng.gen_range_usize(35, 50),
        };
        let k = if count % 10 == 0 {
            *[0i32, 1, 50, 99, 100].get(rng.gen_range_usize(0, 4)).unwrap()
        } else {
            rng.gen_range_i64(0, 100) as i32
        };
        let total = m * n;
        let mut flat: Vec<i32> = Vec::with_capacity(total);
        for _ in 0..total {
            let v = if count % 5 == 0 {
                *[-1000i32, -1, 0, 1, 1000].get(rng.gen_range_usize(0, 4)).unwrap()
            } else {
                rng.gen_range_i64(-1000, 1000) as i32
            };
            flat.push(v);
        }
        let mk = (rng.next_u64() % 5) as u8;
        let (g, kk) = generate_test_case(m, n, &flat, k, mk);
        emit(g, kk, &mut seen, &mut out, &mut count);
    }
}
