use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    values: Vec<i32>,
    mutation_kind: u8,
) -> (grid: Vec<Vec<i32>>)
    requires
        1 <= n <= 200,
        values.len() == n * n,
        forall|k: int| 0 <= k < values.len() ==> -99 <= #[trigger] values[k] <= 99,
    ensures
        1 <= grid.len() <= 200,
        forall |i: int| 0 <= i < grid.len() ==> (#[trigger] grid[i]).len() == grid.len(),
        forall |i: int, j: int| 0 <= i < grid.len() && 0 <= j < grid[i].len()
            ==> -99 <= #[trigger] grid[i][j] <= 99,
{
    // Apply mutation to flat values
    let mut vals = values;

    if mutation_kind == 1 && vals.len() > 0 {
        // set first element to max boundary
        vals.set(0, 99);
    } else if mutation_kind == 2 && vals.len() > 0 {
        // set first element to min boundary
        vals.set(0, -99);
    } else if mutation_kind == 3 && vals.len() > 0 {
        // set first element to zero
        vals.set(0, 0);
    } else if mutation_kind == 4 {
        // set all elements to zero
        let mut k: usize = 0;
        while k < vals.len()
            invariant
                vals.len() == n * n,
                0 <= k <= vals.len(),
                forall|idx: int| 0 <= idx < k ==> vals[idx] == 0i32,
                forall|idx: int| k <= idx < vals.len() ==> -99 <= #[trigger] vals[idx] <= 99,
            decreases vals.len() - k,
        {
            vals.set(k, 0);
            k += 1;
        }
    } else if mutation_kind == 5 && vals.len() > 0 && vals[0] < 99 {
        // nudge first element up
        vals.set(0, (vals[0] + 1) as i32);
    } else if mutation_kind == 6 && vals.len() > 0 && vals[0] > -99 {
        // nudge first element down
        vals.set(0, (vals[0] - 1) as i32);
    } else if mutation_kind == 7 {
        // set all to 99
        let mut k: usize = 0;
        while k < vals.len()
            invariant
                vals.len() == n * n,
                0 <= k <= vals.len(),
                forall|idx: int| 0 <= idx < k ==> vals[idx] == 99i32,
                forall|idx: int| k <= idx < vals.len() ==> -99 <= #[trigger] vals[idx] <= 99,
            decreases vals.len() - k,
        {
            vals.set(k, 99);
            k += 1;
        }
    } else if mutation_kind == 8 {
        // set all to -99
        let mut k: usize = 0;
        while k < vals.len()
            invariant
                vals.len() == n * n,
                0 <= k <= vals.len(),
                forall|idx: int| 0 <= idx < k ==> vals[idx] == -99i32,
                forall|idx: int| k <= idx < vals.len() ==> -99 <= #[trigger] vals[idx] <= 99,
            decreases vals.len() - k,
        {
            vals.set(k, -99);
            k += 1;
        }
    }
    // else: identity (mutation_kind == 0 or fallback)

    // All vals are in range after any mutation
    assert(forall|k: int| 0 <= k < vals.len() ==> -99 <= #[trigger] vals[k] <= 99);

    // Reshape flat array into n×n grid
    let mut grid: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            1 <= n <= 200,
            vals.len() == n * n,
            grid.len() == i,
            0 <= i <= n,
            forall|k: int| 0 <= k < vals.len() ==> -99 <= #[trigger] vals[k] <= 99,
            forall|r: int| 0 <= r < i ==> (#[trigger] grid[r]).len() == n,
            forall|r: int, c: int| 0 <= r < i && 0 <= c < n
                ==> -99 <= #[trigger] grid[r][c] <= 99,
        decreases n - i,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                1 <= n <= 200,
                0 <= i < n,
                0 <= j <= n,
                row.len() == j,
                vals.len() == n * n,
                forall|k: int| 0 <= k < vals.len() ==> -99 <= #[trigger] vals[k] <= 99,
                forall|c: int| 0 <= c < j ==> -99 <= #[trigger] row[c] <= 99,
            decreases n - j,
        {
            assert(i * n + j < n * n) by(nonlinear_arith)
                requires i < n as int, j < n as int, n >= 1,
            {};
            let val = vals[i * n + j];
            row.push(val);
            j += 1;
        }
        assert(row.len() == n);
        grid.push(row);
        i += 1;
    }

    assert(grid.len() == n);

    // Prove the ensures about grid[i].len() == grid.len()
    proof {
        assert(grid.len() == n);
        assert forall|r: int| 0 <= r < grid.len() implies (#[trigger] grid[r]).len() == grid.len() by {
            assert(grid[r].len() == n);
        };
    }

    grid
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

extern crate serde_json;
use serde_json::json;

fn random_flat_grid(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut values = Vec::with_capacity(n * n);
    for _ in 0..n * n {
        values.push(rng.gen_range_i64(-99, 99) as i32);
    }
    values
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1289);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |grid: Vec<Vec<i32>>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        let key = format!("{:?}", grid);
        if !seen.insert(key) { return; }
        let result = Solution::min_falling_path_sum(grid.clone());
        writeln!(out, "{}", json!({"input": {"grid": grid}, "output": result})).unwrap();
        *count += 1;
    };

    // Example 1: [[1,2,3],[4,5,6],[7,8,9]] => 13
    emit(vec![vec![1,2,3], vec![4,5,6], vec![7,8,9]], &mut seen, &mut out, &mut count);
    // Example 2: [[7]] => 7
    emit(vec![vec![7]], &mut seen, &mut out, &mut count);

    // Boundary grids via mutations
    let boundary_sizes: Vec<usize> = vec![1, 2, 3, 5, 10];
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8];
    for &n in &boundary_sizes {
        for &mk in &mutation_kinds {
            if count >= target { break; }
            let values = random_flat_grid(&mut rng, n);
            let grid = generate_test_case(n, values, mk);
            emit(grid, &mut seen, &mut out, &mut count);
        }
    }

    // Diverse size classes with random mutations
    for i in 0..80 {
        if count >= target { break; }
        let n: usize = match i % 6 {
            0 => 1,                                     // 1x1
            1 => rng.gen_range_usize(2, 5),             // tiny
            2 => rng.gen_range_usize(6, 15),            // small
            3 => rng.gen_range_usize(16, 50),           // medium
            4 => rng.gen_range_usize(51, 100),          // large
            _ => rng.gen_range_usize(101, 200),         // max
        };
        let mk = rng.gen_range_usize(0, 8) as u8;
        let values = random_flat_grid(&mut rng, n);
        let grid = generate_test_case(n, values, mk);
        emit(grid, &mut seen, &mut out, &mut count);
    }

    // Fill remaining with identity mutation and random sizes
    while count < target {
        let n = rng.gen_range_usize(1, 200);
        let values = random_flat_grid(&mut rng, n);
        let grid = generate_test_case(n, values, 0);
        emit(grid, &mut seen, &mut out, &mut count);
    }
}
