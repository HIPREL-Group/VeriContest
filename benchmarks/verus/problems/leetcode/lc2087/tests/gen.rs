use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    row_costs: Vec<i32>,
    col_costs: Vec<i32>,
    start_row_raw: usize,
    home_row_raw: usize,
    start_col_raw: usize,
    home_col_raw: usize,
    mutation_kind: u8,
) -> (result: (Vec<i32>, Vec<i32>, Vec<i32>, Vec<i32>))
    requires
        1 <= row_costs.len() <= 100_000,
        1 <= col_costs.len() <= 100_000,
        forall |i: int| 0 <= i < row_costs.len() ==> 0 <= #[trigger] row_costs[i] <= 10_000,
        forall |i: int| 0 <= i < col_costs.len() ==> 0 <= #[trigger] col_costs[i] <= 10_000,
    ensures
        result.0.len() == 2,
        result.1.len() == 2,
        1 <= result.2.len() <= 100_000,
        1 <= result.3.len() <= 100_000,
        forall |i: int| 0 <= i < result.2.len() ==> 0 <= #[trigger] result.2[i] <= 10_000,
        forall |i: int| 0 <= i < result.3.len() ==> 0 <= #[trigger] result.3[i] <= 10_000,
        0 <= result.0[0] < result.2.len(),
        0 <= result.1[0] < result.2.len(),
        0 <= result.0[1] < result.3.len(),
        0 <= result.1[1] < result.3.len(),
{
    let sr = (start_row_raw % row_costs.len()) as i32;
    let hr = (home_row_raw % row_costs.len()) as i32;
    let sc = (start_col_raw % col_costs.len()) as i32;
    let hc = (home_col_raw % col_costs.len()) as i32;

    let mut start_pos: Vec<i32> = Vec::new();
    let mut home_pos: Vec<i32> = Vec::new();

    if mutation_kind == 0 {
        // default: use computed indices
        start_pos.push(sr);
        start_pos.push(sc);
        home_pos.push(hr);
        home_pos.push(hc);
    } else if mutation_kind == 1 {
        // same position (zero cost)
        start_pos.push(sr);
        start_pos.push(sc);
        home_pos.push(sr);
        home_pos.push(sc);
    } else if mutation_kind == 2 {
        // swap start and home
        start_pos.push(hr);
        start_pos.push(hc);
        home_pos.push(sr);
        home_pos.push(sc);
    } else if mutation_kind == 3 {
        // start at (0, 0)
        start_pos.push(0);
        start_pos.push(0);
        home_pos.push(hr);
        home_pos.push(hc);
    } else if mutation_kind == 4 {
        // same row, different columns (only column movement)
        start_pos.push(sr);
        start_pos.push(sc);
        home_pos.push(sr);
        home_pos.push(hc);
    } else if mutation_kind == 5 {
        // same column, different rows (only row movement)
        start_pos.push(sr);
        start_pos.push(sc);
        home_pos.push(hr);
        home_pos.push(sc);
    } else if mutation_kind == 6 {
        // home at (0, 0)
        start_pos.push(sr);
        start_pos.push(sc);
        home_pos.push(0);
        home_pos.push(0);
    } else {
        // fallback: same as default
        start_pos.push(sr);
        start_pos.push(sc);
        home_pos.push(hr);
        home_pos.push(hc);
    }

    (start_pos, home_pos, row_costs, col_costs)
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

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    use std::io::Write;

    // Example inputs from problem description
    let examples: Vec<(Vec<i32>, Vec<i32>, Vec<i32>, Vec<i32>)> = vec![
        (vec![1, 0], vec![2, 3], vec![5, 4, 3], vec![8, 2, 6, 7]),
        (vec![0, 0], vec![0, 0], vec![5], vec![26]),
    ];

    for (sp, hp, rc, cc) in &examples {
        let result = Solution::min_cost(sp.clone(), hp.clone(), rc.clone(), cc.clone());
        writeln!(out, "{}", json!({
            "input": {"start_pos": sp, "home_pos": hp, "row_costs": rc, "col_costs": cc},
            "output": result
        })).unwrap();
    }

    for i in 0..count {
        // Size classes for array lengths
        let m: usize = match i % 5 {
            0 => rng.gen_range_usize(1, 5),         // tiny
            1 => rng.gen_range_usize(1, 10),         // small
            2 => rng.gen_range_usize(11, 100),       // medium
            3 => rng.gen_range_usize(101, 1000),     // large
            _ => rng.gen_range_usize(1001, 10_000),  // max-ish
        };
        let n: usize = match i % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 1000),
            _ => rng.gen_range_usize(1001, 10_000),
        };

        // Build cost arrays with boundary values mixed in
        let mut row_costs: Vec<i32> = Vec::with_capacity(m);
        for j in 0..m {
            let v = if j == 0 && i % 10 == 0 {
                0 // boundary: zero cost
            } else if j == m - 1 && i % 10 == 1 {
                10_000 // boundary: max cost
            } else {
                rng.gen_range_i64(0, 10_000) as i32
            };
            row_costs.push(v);
        }

        let mut col_costs: Vec<i32> = Vec::with_capacity(n);
        for j in 0..n {
            let v = if j == 0 && i % 10 == 2 {
                0
            } else if j == n - 1 && i % 10 == 3 {
                10_000
            } else {
                rng.gen_range_i64(0, 10_000) as i32
            };
            col_costs.push(v);
        }

        let start_row_raw = rng.gen_range_usize(0, usize::MAX / 2);
        let home_row_raw = rng.gen_range_usize(0, usize::MAX / 2);
        let start_col_raw = rng.gen_range_usize(0, usize::MAX / 2);
        let home_col_raw = rng.gen_range_usize(0, usize::MAX / 2);
        let mutation_kind = (i % 8) as u8;

        let (start_pos, home_pos, rc, cc) = generate_test_case(
            row_costs, col_costs,
            start_row_raw, home_row_raw,
            start_col_raw, home_col_raw,
            mutation_kind,
        );

        let result = Solution::min_cost(
            start_pos.clone(), home_pos.clone(), rc.clone(), cc.clone(),
        );

        writeln!(out, "{}", json!({
            "input": {"start_pos": start_pos, "home_pos": home_pos, "row_costs": rc, "col_costs": cc},
            "output": result
        })).unwrap();
    }
}
