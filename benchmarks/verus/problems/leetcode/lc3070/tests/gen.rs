use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    grid: Vec<Vec<i32>>,
    k: i32,
    mutation_kind: u8,
) -> (result: (Vec<Vec<i32>>, i32))
    requires
        1 <= grid.len() <= 1000,
        forall |r: int| 0 <= r < grid.len() ==> #[trigger] grid[r].len() == grid[0].len(),
        1 <= grid[0].len() <= 1000,
        forall |r: int, c: int| 0 <= r < grid.len() && 0 <= c < grid[r].len()
            ==> 0 <= #[trigger] grid[r][c] <= 1000,
        1 <= k <= 1_000_000_000,
    ensures
        1 <= result.0.len() <= 1000,
        forall |r: int| 0 <= r < result.0.len() ==> #[trigger] result.0[r].len() == result.0[0].len(),
        1 <= result.0[0].len() <= 1000,
        forall |r: int, c: int| 0 <= r < result.0.len() && 0 <= c < result.0[r].len()
            ==> 0 <= #[trigger] result.0[r][c] <= 1000,
        1 <= result.1 <= 1_000_000_000,
{
    if mutation_kind == 0 {
        // identity
        (grid, k)
    } else if mutation_kind == 1 || mutation_kind == 2 {
        // all-zeros (1) or all-fill with value 1000 (2)
        let fill: i32 = if mutation_kind == 1 { 0 } else { 1000 };
        let rows = grid.len();
        let cols = grid[0].len();
        let mut res: Vec<Vec<i32>> = Vec::new();
        let mut i: usize = 0;
        while i < rows
            invariant
                0 <= i <= rows,
                1 <= rows <= 1000,
                1 <= cols <= 1000,
                fill == 0 || fill == 1000,
                res.len() == i as nat,
                forall|r: int| 0 <= r < i as int ==> (#[trigger] res[r]).len() == cols,
                forall|r: int, c: int| 0 <= r < i as int && 0 <= c < cols as int
                    ==> 0 <= #[trigger] res[r][c] <= 1000,
            decreases rows - i,
        {
            let mut row: Vec<i32> = Vec::new();
            let mut j: usize = 0;
            while j < cols
                invariant
                    0 <= j <= cols,
                    1 <= cols <= 1000,
                    fill == 0 || fill == 1000,
                    row.len() == j as nat,
                    forall|c: int| 0 <= c < j as int ==> 0 <= #[trigger] row[c] <= 1000,
                decreases cols - j,
            {
                row.push(fill);
                j += 1;
            }
            res.push(row);
            i += 1;
        }
        (res, k)
    } else if mutation_kind == 3 {
        // clamp k to 1 (minimum boundary)
        (grid, 1)
    } else if mutation_kind == 4 {
        // set k to max boundary
        (grid, 1_000_000_000)
    } else {
        // fallback: identity
        (grid, k)
    }
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
        assert!(lo <= hi);
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

struct Solution;
include!("../code.rs");

fn random_grid(rng: &mut Rng, m: usize, n: usize, max_val: i32) -> Vec<Vec<i32>> {
    let mut mat = Vec::with_capacity(m);
    for _ in 0..m {
        let mut row = Vec::with_capacity(n);
        for _ in 0..n {
            row.push(rng.gen_range_i64(0, max_val as i64) as i32);
        }
        mat.push(row);
    }
    mat
}

fn all_val_grid(m: usize, n: usize, val: i32) -> Vec<Vec<i32>> {
    let mut mat = Vec::with_capacity(m);
    for _ in 0..m {
        mat.push(vec![val; n]);
    }
    mat
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(3070);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |grid: Vec<Vec<i32>>, k: i32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count { return; }
        let key = format!("{:?}_{}", grid, k);
        if !seen.insert(key) { return; }
        let output = Solution::count_submatrices(grid.clone(), k);
        writeln!(out, "{}", json!({"input": {"grid": grid, "k": k}, "output": output})).unwrap();
        *count += 1;
    };

    // Example test cases from description.md
    let ex1 = vec![vec![7,6,3], vec![6,6,1]];
    emit(ex1, 18, &mut seen, &mut out, &mut count);

    let ex2 = vec![vec![7,2,9], vec![1,5,0], vec![2,6,6]];
    emit(ex2, 20, &mut seen, &mut out, &mut count);

    // Structured seed grids with all mutation kinds
    let seed_grids: Vec<(Vec<Vec<i32>>, i32)> = vec![
        // 1x1 grids
        (vec![vec![0]], 1),
        (vec![vec![1000]], 1000),
        (vec![vec![500]], 500),
        // 1xN
        (vec![vec![1, 2, 3, 4, 5]], 10),
        (vec![vec![0, 0, 0, 0, 0]], 1),
        // Mx1
        (vec![vec![1], vec![2], vec![3]], 5),
        (vec![vec![0], vec![0], vec![0]], 1),
        // Small squares
        (vec![vec![1, 2], vec![3, 4]], 10),
        (vec![vec![0, 0], vec![0, 0]], 1),
        (vec![vec![1000, 1000], vec![1000, 1000]], 1_000_000_000),
        // 3x3
        (all_val_grid(3, 3, 0), 1),
        (all_val_grid(3, 3, 1), 9),
        (all_val_grid(3, 3, 1000), 1_000_000_000),
        // Rectangular
        (vec![vec![1, 2, 3, 4], vec![5, 6, 7, 8]], 20),
        (vec![vec![1, 2], vec![3, 4], vec![5, 6], vec![7, 8]], 30),
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4];

    for (grid, k) in &seed_grids {
        for &mk in &mutation_kinds {
            if count >= target_count { break; }
            let (res_grid, res_k) = generate_test_case(grid.clone(), *k, mk);
            emit(res_grid, res_k, &mut seen, &mut out, &mut count);
        }
    }

    // Random grids across size classes
    while count < target_count {
        let (m, n) = match count % 7 {
            0 => (1, 1),
            1 => (rng.gen_range_usize(1, 3), rng.gen_range_usize(1, 3)),
            2 => (rng.gen_range_usize(2, 10), rng.gen_range_usize(2, 10)),
            3 => (rng.gen_range_usize(5, 30), rng.gen_range_usize(5, 30)),
            4 => (rng.gen_range_usize(10, 50), rng.gen_range_usize(10, 50)),
            5 => (rng.gen_range_usize(50, 100), rng.gen_range_usize(50, 100)),
            _ => (rng.gen_range_usize(100, 300), rng.gen_range_usize(100, 300)),
        };

        let max_val: i32 = match count % 5 {
            0 => 1,
            1 => 10,
            2 => 100,
            3 => 500,
            _ => 1000,
        };

        let grid = if count % 10 == 0 {
            all_val_grid(m, n, 0)
        } else if count % 10 == 5 {
            all_val_grid(m, n, max_val)
        } else {
            random_grid(&mut rng, m, n, max_val)
        };

        let k = match count % 6 {
            0 => 1,
            1 => rng.gen_range_i64(1, 100) as i32,
            2 => rng.gen_range_i64(100, 10000) as i32,
            3 => rng.gen_range_i64(10000, 1_000_000) as i32,
            4 => rng.gen_range_i64(1_000_000, 1_000_000_000) as i32,
            _ => 1_000_000_000,
        };

        let mk = rng.gen_range_usize(0, 4) as u8;
        let (res_grid, res_k) = generate_test_case(grid, k, mk);
        emit(res_grid, res_k, &mut seen, &mut out, &mut count);
    }
}
