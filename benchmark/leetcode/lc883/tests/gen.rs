use vstd::prelude::*;

verus! {

pub fn generate_test_case(grid: Vec<Vec<i32>>, mutation_kind: u8) -> (result: Vec<Vec<i32>>)
    requires
        1 <= grid.len() <= 50,
        forall|i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == grid.len(),
        forall|i: int, j: int| 0 <= i < grid.len() && 0 <= j < grid.len() ==> 0 <= #[trigger] grid[i][j] <= 50,
    ensures
        1 <= result.len() <= 50,
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i].len() == result.len(),
        forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result.len() ==> 0 <= #[trigger] result[i][j] <= 50,
{
    if mutation_kind == 0 {
        // identity
        grid
    } else {
        let n = grid.len();
        let fill_val: i32 = if mutation_kind == 1 {
            0i32
        } else if mutation_kind == 2 {
            50i32
        } else if mutation_kind == 3 {
            1i32
        } else if mutation_kind == 4 {
            25i32
        } else {
            0i32
        };

        let mut result: Vec<Vec<i32>> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                1 <= n <= 50,
                0 <= fill_val <= 50,
                result.len() == i,
                forall|r: int| 0 <= r < i as int ==> (#[trigger] result[r]).len() == n,
                forall|r: int, c: int|
                    0 <= r < i as int && 0 <= c < n as int
                    ==> 0 <= #[trigger] result[r][c] <= 50,
            decreases n - i,
        {
            let mut row: Vec<i32> = Vec::new();
            let mut j: usize = 0;
            while j < n
                invariant
                    0 <= j <= n,
                    1 <= n <= 50,
                    0 <= fill_val <= 50,
                    row.len() == j,
                    forall|c: int|
                        0 <= c < j as int
                        ==> 0 <= #[trigger] row[c] <= 50,
                decreases n - j,
            {
                row.push(fill_val);
                j = j + 1;
            }
            assert(row.len() == n);
            result.push(row);
            i = i + 1;
        }
        assert(result.len() == n);
        result
    }
}

} // verus!

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }

    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
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

extern crate serde_json;
use serde_json::json;

fn random_grid(rng: &mut Rng, n: usize) -> Vec<Vec<i32>> {
    let mut grid = Vec::with_capacity(n);
    for _ in 0..n {
        let mut row = Vec::with_capacity(n);
        for _ in 0..n {
            row.push(rng.gen_range_i64(0, 50) as i32);
        }
        grid.push(row);
    }
    grid
}

fn main() {
    use std::io::Write;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut total = 0usize;

    let mut emit = |grid: Vec<Vec<i32>>, out: &mut std::io::BufWriter<std::fs::File>, total: &mut usize, count: usize| {
        if *total >= count { return; }
        let output = Solution::projection_area(grid.clone());
        writeln!(out, "{}", json!({"input": {"grid": grid}, "output": output})).unwrap();
        *total += 1;
    };

    // Example test cases from description.md
    emit(vec![vec![1, 2], vec![3, 4]], &mut out, &mut total, count);
    emit(vec![vec![2]], &mut out, &mut total, count);
    emit(vec![vec![1, 0], vec![0, 2]], &mut out, &mut total, count);

    // Seed grids with mutations
    let seeds: Vec<Vec<Vec<i32>>> = vec![
        vec![vec![1, 2], vec![3, 4]],
        vec![vec![2]],
        vec![vec![1, 0], vec![0, 2]],
        vec![vec![0]],
        vec![vec![50]],
        vec![vec![0, 0], vec![0, 0]],
        vec![vec![50, 50], vec![50, 50]],
        vec![vec![0, 50, 0], vec![50, 0, 50], vec![0, 50, 0]],
    ];
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4];

    for grid in &seeds {
        for &mk in &mutation_kinds {
            if total >= count { break; }
            let result = generate_test_case(grid.clone(), mk);
            emit(result, &mut out, &mut total, count);
        }
    }

    // Random grids across size classes with random mutations
    while total < count {
        let n = match total % 5 {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(1, 5),
            2 => rng.gen_range_usize(5, 15),
            3 => rng.gen_range_usize(15, 35),
            _ => rng.gen_range_usize(35, 50),
        };
        let grid = random_grid(&mut rng, n);
        let mk = rng.gen_range_usize(0, 4) as u8;
        let result = generate_test_case(grid, mk);
        emit(result, &mut out, &mut total, count);
    }
}
