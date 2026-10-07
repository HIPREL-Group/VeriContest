use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    rows: i32,
    cols: i32,
    r_center: i32,
    c_center: i32,
    mutation_kind: u8,
) -> (result: (i32, i32, i32, i32))
    requires
        1 <= rows <= 100,
        1 <= cols <= 100,
        0 <= r_center < rows,
        0 <= c_center < cols,
    ensures
        1 <= result.0 <= 100,
        1 <= result.1 <= 100,
        0 <= result.2 < result.0,
        0 <= result.3 < result.1,
{
    if mutation_kind == 0 {
        (rows, cols, r_center, c_center)
    } else if mutation_kind == 1 {
        (1, cols, 0, c_center)
    } else if mutation_kind == 2 {
        (rows, 1, r_center, 0)
    } else if mutation_kind == 3 {
        (100, cols, r_center, c_center)
    } else if mutation_kind == 4 {
        (rows, 100, r_center, c_center)
    } else if mutation_kind == 5 {
        (rows, cols, 0, 0)
    } else if mutation_kind == 6 {
        (rows, cols, rows - 1, cols - 1)
    } else if mutation_kind == 7 {
        (rows, cols, 0, cols - 1)
    } else if mutation_kind == 8 {
        (rows, cols, rows - 1, 0)
    } else if mutation_kind == 9 {
        (1, 1, 0, 0)
    } else if mutation_kind == 10 {
        (100, 100, 0, 0)
    } else if mutation_kind == 11 {
        (100, 100, 99, 99)
    } else if mutation_kind == 12 {
        (rows, rows, r_center, if c_center < rows { c_center } else { rows - 1 })
    } else {
        (rows, cols, r_center, c_center)
    }
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

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |rows: i32, cols: i32, r_center: i32, c_center: i32,
                    seen: &mut HashSet<(i32,i32,i32,i32)>,
                    out: &mut std::io::BufWriter<std::fs::File>,
                    count: &mut usize| {
        if *count >= goal { return; }
        let key = (rows, cols, r_center, c_center);
        if !seen.insert(key) { return; }
        let output = Solution::all_cells_dist_order(rows, cols, r_center, c_center);
        writeln!(out, "{}", json!({
            "input": {"rows": rows, "cols": cols, "rCenter": r_center, "cCenter": c_center},
            "output": output
        })).unwrap();
        *count += 1;
    };

    // Example inputs from description
    let examples: Vec<(i32, i32, i32, i32)> = vec![
        (1, 2, 0, 0),
        (2, 2, 0, 1),
        (2, 3, 1, 2),
    ];
    for (r, c, rc, cc) in &examples {
        emit(*r, *c, *rc, *cc, &mut seen, &mut out, &mut count);
    }

    // Interesting seed configurations
    let seeds: Vec<(i32, i32, i32, i32)> = vec![
        (1, 1, 0, 0),
        (1, 100, 0, 0),
        (1, 100, 0, 99),
        (1, 100, 0, 50),
        (100, 1, 0, 0),
        (100, 1, 99, 0),
        (100, 1, 50, 0),
        (100, 100, 0, 0),
        (100, 100, 99, 99),
        (100, 100, 50, 50),
        (100, 100, 0, 99),
        (100, 100, 99, 0),
        (10, 10, 5, 5),
        (3, 3, 1, 1),
        (5, 5, 0, 0),
        (5, 5, 4, 4),
        (2, 2, 0, 0),
        (2, 2, 1, 1),
        (50, 50, 25, 25),
        (10, 1, 5, 0),
        (1, 10, 0, 5),
    ];

    for (r, c, rc, cc) in &seeds {
        for mk in 0..=12u8 {
            if count >= goal { break; }
            let (nr, nc, nrc, ncc) = generate_test_case(*r, *c, *rc, *cc, mk);
            emit(nr, nc, nrc, ncc, &mut seen, &mut out, &mut count);
        }
        if count >= goal { break; }
    }

    while count < goal {
        let rows = rng.gen_range_i64(1, 100) as i32;
        let cols = rng.gen_range_i64(1, 100) as i32;
        let r_center = rng.gen_range_i64(0, rows as i64 - 1) as i32;
        let c_center = rng.gen_range_i64(0, cols as i64 - 1) as i32;
        let mk = rng.gen_range_usize(0, 12) as u8;
        let (nr, nc, nrc, ncc) = generate_test_case(rows, cols, r_center, c_center, mk);
        emit(nr, nc, nrc, ncc, &mut seen, &mut out, &mut count);
    }
}
