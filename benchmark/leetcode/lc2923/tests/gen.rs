use vstd::prelude::*;

verus! {

pub open spec fn is_champion(grid: Seq<Vec<i32>>, c: int) -> bool {
    &&& 0 <= c < grid.len()
    &&& forall |j: int| 0 <= j < grid.len() && j != c ==> #[trigger] grid[c][j] == 1
}

/// Spec-level value of cell (r, c) in the constructed tournament grid.
pub open spec fn cell_val(r: int, c: int, champion: int, reverse: bool) -> i32 {
    if r == c { 0i32 }
    else if r == champion { 1i32 }
    else if c == champion { 0i32 }
    else if !reverse {
        if r < c { 1i32 } else { 0i32 }
    } else {
        if r > c { 1i32 } else { 0i32 }
    }
}

proof fn cell_val_binary(r: int, c: int, champion: int, reverse: bool)
    ensures cell_val(r, c, champion, reverse) == 0 || cell_val(r, c, champion, reverse) == 1
{
}

proof fn cell_val_antisymmetric(r: int, c: int, champion: int, reverse: bool)
    requires r != c
    ensures cell_val(r, c, champion, reverse) + cell_val(c, r, champion, reverse) == 1
{
}

pub fn generate_test_case(n: usize, champion: usize, mutation_kind: u8) -> (grid: Vec<Vec<i32>>)
    requires
        2 <= n <= 100,
        0 <= champion < n,
    ensures
        2 <= grid.len() <= 100,
        forall |i: int| 0 <= i < grid.len() ==> #[trigger] grid[i].len() == grid.len(),
        forall |i: int, j: int| 0 <= i < grid.len() && 0 <= j < grid.len() ==>
            (#[trigger] grid[i][j] == 0 || grid[i][j] == 1),
        forall |i: int| 0 <= i < grid.len() ==> grid[i][i] == 0,
        forall |i: int, j: int| 0 <= i < grid.len() && 0 <= j < grid.len() && i != j ==>
            grid[i][j] + grid[j][i] == 1,
        exists |c: int| is_champion(grid@, c),
{
    let reverse = mutation_kind != 0;
    let mut grid: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            grid.len() == i,
            0 <= i <= n,
            2 <= n <= 100,
            0 <= champion < n,
            forall |r: int| 0 <= r < i ==> (#[trigger] grid[r]).len() == n,
            forall |r: int, c: int| 0 <= r < i && 0 <= c < n ==>
                #[trigger] grid[r][c] == cell_val(r, c, champion as int, reverse),
        decreases n - i,
    {
        let mut row: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                row.len() == j,
                0 <= j <= n,
                0 <= i < n,
                2 <= n <= 100,
                0 <= champion < n,
                forall |c: int| 0 <= c < j ==>
                    #[trigger] row[c] == cell_val(i as int, c, champion as int, reverse),
            decreases n - j,
        {
            let v: i32;
            if i == j {
                v = 0;
            } else if i == champion {
                v = 1;
            } else if j == champion {
                v = 0;
            } else if !reverse {
                if i < j { v = 1; } else { v = 0; }
            } else {
                if i > j { v = 1; } else { v = 0; }
            }
            row.push(v);
            j += 1;
        }
        grid.push(row);
        i += 1;
    }

    proof {
        assert forall |r: int, c: int| 0 <= r < grid.len() && 0 <= c < grid.len()
            implies (#[trigger] grid[r][c] == 0 || grid[r][c] == 1) by {
            cell_val_binary(r, c, champion as int, reverse);
        };

        assert forall |r: int| 0 <= r < grid.len()
            implies grid[r][r] == 0 by {};

        assert forall |r: int, c: int|
            0 <= r < grid.len() && 0 <= c < grid.len() && r != c
            implies grid[r][c] + grid[c][r] == 1 by {
            cell_val_antisymmetric(r, c, champion as int, reverse);
        };

        assert forall |j: int| 0 <= j < grid.len() && j != champion as int
            implies #[trigger] grid[champion as int][j] == 1 by {};
        assert(is_champion(grid@, champion as int));
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

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let (lo, hi) = if lo <= hi { (lo, hi) } else { (hi, lo) };
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

struct Solution;
include!("../code.rs");

fn make_grid(n: usize, champion: usize, mutation_kind: u8) -> Vec<Vec<i32>> {
    generate_test_case(n, champion, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2923);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut total = 0usize;

    let mut emit = |grid: Vec<Vec<i32>>, seen: &mut HashSet<String>,
                    out: &mut std::io::BufWriter<std::fs::File>, total: &mut usize| {
        let key = format!("{:?}", grid);
        if *total >= count || !seen.insert(key) {
            return;
        }
        let output = Solution::find_champion(grid.clone());
        writeln!(out, "{}", json!({
            "input": {"grid": grid},
            "output": output
        })).unwrap();
        *total += 1;
    };

    // Example 1: [[0,1],[0,0]] -> 0
    emit(vec![vec![0,1], vec![0,0]], &mut seen, &mut out, &mut total);
    // Example 2: [[0,0,1],[1,0,1],[0,0,0]] -> 1
    emit(vec![vec![0,0,1], vec![1,0,1], vec![0,0,0]], &mut seen, &mut out, &mut total);

    // Systematic: small sizes × champion positions × mutation kinds
    let sizes: Vec<usize> = vec![2, 3, 4, 5, 10, 20, 50, 100];
    let mutation_kinds: Vec<u8> = vec![0, 1];

    for &n in &sizes {
        for &mk in &mutation_kinds {
            // Champion at first, last, and middle positions
            let positions: Vec<usize> = vec![0, n - 1, n / 2];
            for &champ in &positions {
                let grid = make_grid(n, champ, mk);
                emit(grid, &mut seen, &mut out, &mut total);
            }
        }
    }

    // Random test cases to fill remaining
    let mut _attempts_0 = 0usize;
    while total < count {
        _attempts_0 += 1; if _attempts_0 > 10000 { break; }
        // Size classes
        let n = match total % 5 {
            0 => rng.gen_range_usize(2, 5),    // tiny
            1 => rng.gen_range_usize(2, 10),   // small
            2 => rng.gen_range_usize(11, 30),  // medium
            3 => rng.gen_range_usize(31, 70),  // large
            _ => rng.gen_range_usize(71, 100), // max
        };
        let champion = rng.gen_range_usize(0, n - 1);
        let mk = rng.gen_range_usize(0, 1) as u8;
        let grid = make_grid(n, champion, mk);
        emit(grid, &mut seen, &mut out, &mut total);
    }
}
