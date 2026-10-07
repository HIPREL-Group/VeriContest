use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    rows: usize,
    cols: usize,
    val_a: i32,
    val_b: i32,
    val_c: i32,
    mutation_kind: u8,
) -> (grid: Vec<Vec<i32>>)
    requires
        3 <= rows <= 150,
        3 <= cols <= 150,
        0 <= val_a <= 1_000_000i32,
        0 <= val_b <= 1_000_000i32,
        0 <= val_c <= 1_000_000i32,
    ensures
        3 <= grid.len() <= 150,
        forall |i: int| 0 <= i < grid.len() ==> 3 <= #[trigger] grid[i].len() <= 150,
        forall |i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == grid[0].len(),
        forall |i: int, j: int| 0 <= i < grid.len() && 0 <= j < grid[0].len() ==> 0 <= #[trigger] grid[i][j] <= 1_000_000,
{
    let mut grid: Vec<Vec<i32>> = Vec::new();
    let mut r: usize = 0;
    while r < rows
        invariant
            0 <= r <= rows,
            grid.len() == r,
            3 <= rows <= 150,
            3 <= cols <= 150,
            0 <= val_a <= 1_000_000i32,
            0 <= val_b <= 1_000_000i32,
            0 <= val_c <= 1_000_000i32,
            forall |i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == cols,
            forall |i: int, j: int| 0 <= i < grid.len() && 0 <= j < grid[i].len()
                ==> 0 <= #[trigger] grid[i][j] <= 1_000_000,
        decreases rows - r,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut c: usize = 0;
        while c < cols
            invariant
                0 <= c <= cols,
                row.len() == c,
                0 <= val_a <= 1_000_000i32,
                0 <= val_b <= 1_000_000i32,
                0 <= val_c <= 1_000_000i32,
                r <= 149,
                cols <= 150,
                forall |j: int| 0 <= j < row.len() ==> 0 <= #[trigger] row[j] <= 1_000_000,
            decreases cols - c,
        {
            let v: i32 = if mutation_kind == 0 {
                val_a                                           // uniform a
            } else if mutation_kind == 1 {
                val_b                                           // uniform b
            } else if mutation_kind == 2 {
                0i32                                            // all zeros
            } else if mutation_kind == 3 {
                1_000_000i32                                    // all max
            } else if mutation_kind == 4 {
                if (r + c) % 2 == 0 { val_a } else { val_b }   // checkerboard
            } else if mutation_kind == 5 {
                if r < rows / 2 { val_a } else { val_b }       // horizontal split
            } else if mutation_kind == 6 {
                val_c                                           // uniform c
            } else if mutation_kind == 7 {
                val_a / 2                                       // halved a
            } else {
                val_a                                           // fallback
            };
            row.push(v);
            c = c + 1;
        }
        grid.push(row);
        r = r + 1;
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

fn gen(rows: usize, cols: usize, val_a: i32, val_b: i32, val_c: i32, mk: u8) -> Vec<Vec<i32>> {
    generate_test_case(rows, cols, val_a, val_b, val_c, mk)
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2428);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);
    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut emitted = 0usize;

    let mut emit = |grid: Vec<Vec<i32>>, out: &mut std::io::BufWriter<std::fs::File>, emitted: &mut usize| {
        if *emitted >= count { return; }
        let output = Solution::max_sum(grid.clone());
        writeln!(out, "{}", json!({"input": {"grid": grid}, "output": output})).unwrap();
        *emitted += 1;
    };

    // Example inputs from description.md
    emit(
        vec![vec![6,2,1,3],vec![4,2,1,5],vec![9,2,8,7],vec![4,1,2,9]],
        &mut out, &mut emitted,
    );
    emit(
        vec![vec![1,2,3],vec![4,5,6],vec![7,8,9]],
        &mut out, &mut emitted,
    );

    let boundary_vals: Vec<i32> = vec![0, 1, 2, 999_999, 1_000_000, 500_000, 100, 42];
    let sizes: Vec<(usize, usize)> = vec![
        (3, 3), (3, 150), (150, 3), (150, 150),
        (4, 4), (5, 5), (10, 10), (50, 50),
    ];
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7];

    // Structured sweep: boundary values × sizes × mutations
    for &(rows, cols) in &sizes {
        for &mk in &mutation_kinds {
            if emitted >= count { break; }
            let va = boundary_vals[emitted % boundary_vals.len()];
            let vb = boundary_vals[(emitted + 1) % boundary_vals.len()];
            let vc = boundary_vals[(emitted + 2) % boundary_vals.len()];
            emit(gen(rows, cols, va, vb, vc, mk), &mut out, &mut emitted);
        }
    }

    // Random test cases with diverse size classes
    while emitted < count {
        let rows = match emitted % 5 {
            0 => rng.gen_range_usize(3, 5),
            1 => rng.gen_range_usize(3, 10),
            2 => rng.gen_range_usize(11, 50),
            3 => rng.gen_range_usize(51, 100),
            _ => rng.gen_range_usize(101, 150),
        };
        let cols = match emitted % 7 {
            0 => rng.gen_range_usize(3, 5),
            1 => rng.gen_range_usize(3, 10),
            2 => rng.gen_range_usize(11, 50),
            3 => rng.gen_range_usize(51, 100),
            4 | 5 => rng.gen_range_usize(101, 150),
            _ => rng.gen_range_usize(3, 150),
        };
        let val_a = if emitted % 5 == 0 {
            [0i32, 1_000_000, 0, 1, 500_000][emitted % 5]
        } else {
            rng.gen_range_i64(0, 1_000_000) as i32
        };
        let val_b = rng.gen_range_i64(0, 1_000_000) as i32;
        let val_c = rng.gen_range_i64(0, 1_000_000) as i32;
        let mk = rng.gen_range_usize(0, 7) as u8;
        emit(gen(rows, cols, val_a, val_b, val_c, mk), &mut out, &mut emitted);
    }
}
