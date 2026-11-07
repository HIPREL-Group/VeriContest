use vstd::prelude::*;

verus! {

fn build_points(x0: i32, y0: i32, x1: i32, y1: i32, x2: i32, y2: i32) -> (result: Vec<Vec<i32>>)
    requires
        0 <= x0 <= 100,
        0 <= y0 <= 100,
        0 <= x1 <= 100,
        0 <= y1 <= 100,
        0 <= x2 <= 100,
        0 <= y2 <= 100,
    ensures
        result.len() == 3,
        result[0].len() == 2,
        result[1].len() == 2,
        result[2].len() == 2,
        0 <= result[0][0] <= 100,
        0 <= result[0][1] <= 100,
        0 <= result[1][0] <= 100,
        0 <= result[1][1] <= 100,
        0 <= result[2][0] <= 100,
        0 <= result[2][1] <= 100,
{
    let mut p0: Vec<i32> = Vec::new();
    p0.push(x0);
    p0.push(y0);
    let mut p1: Vec<i32> = Vec::new();
    p1.push(x1);
    p1.push(y1);
    let mut p2: Vec<i32> = Vec::new();
    p2.push(x2);
    p2.push(y2);
    let mut pts: Vec<Vec<i32>> = Vec::new();
    pts.push(p0);
    pts.push(p1);
    pts.push(p2);
    pts
}

pub fn generate_test_case(
    x0: i32, y0: i32,
    x1: i32, y1: i32,
    x2: i32, y2: i32,
    mutation_kind: u8,
) -> (result: Vec<Vec<i32>>)
    requires
        0 <= x0 <= 100,
        0 <= y0 <= 100,
        0 <= x1 <= 100,
        0 <= y1 <= 100,
        0 <= x2 <= 100,
        0 <= y2 <= 100,
    ensures
        result.len() == 3,
        result[0].len() == 2,
        result[1].len() == 2,
        result[2].len() == 2,
        0 <= result[0][0] <= 100,
        0 <= result[0][1] <= 100,
        0 <= result[1][0] <= 100,
        0 <= result[1][1] <= 100,
        0 <= result[2][0] <= 100,
        0 <= result[2][1] <= 100,
{
    if mutation_kind == 0 {
        // identity
        build_points(x0, y0, x1, y1, x2, y2)
    } else if mutation_kind == 1 && x0 < 100 {
        // nudge x0 up
        build_points(x0 + 1, y0, x1, y1, x2, y2)
    } else if mutation_kind == 2 && y0 > 0 {
        // nudge y0 down
        build_points(x0, y0 - 1, x1, y1, x2, y2)
    } else if mutation_kind == 3 {
        // all coords zero (collinear: all same point)
        build_points(0, 0, 0, 0, 0, 0)
    } else if mutation_kind == 4 {
        // all coords max boundary
        build_points(100, 100, 100, 100, 100, 100)
    } else if mutation_kind == 5 {
        // duplicate point 0 as point 2 (collinear)
        build_points(x0, y0, x1, y1, x0, y0)
    } else if mutation_kind == 6 {
        // swap points 0 and 1
        build_points(x1, y1, x0, y0, x2, y2)
    } else if mutation_kind == 7 {
        // all y coords = y0 (horizontal line, collinear)
        build_points(x0, y0, x1, y0, x2, y0)
    } else if mutation_kind == 8 {
        // halve all coords
        build_points(x0 / 2, y0 / 2, x1 / 2, y1 / 2, x2 / 2, y2 / 2)
    } else if mutation_kind == 9 {
        // all x coords = x0 (vertical line, collinear)
        build_points(x0, y0, x0, y1, x0, y2)
    } else {
        // fallback: identity
        build_points(x0, y0, x1, y1, x2, y2)
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

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count_goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |pts: Vec<Vec<i32>>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        let key = format!("{:?}", pts);
        if *count >= count_goal || !seen.insert(key) {
            return;
        }
        let output = Solution::is_boomerang(pts.clone());
        writeln!(out, "{}", json!({"input": {"points": pts}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<(i32,i32,i32,i32,i32,i32)> = vec![
        (1, 1, 2, 3, 3, 2),  // true
        (1, 1, 2, 2, 3, 3),  // false (collinear)
    ];
    for &(x0, y0, x1, y1, x2, y2) in &examples {
        let pts = generate_test_case(x0, y0, x1, y1, x2, y2, 0);
        emit(pts, &mut seen, &mut out, &mut count);
    }

    // Interesting seed points (boundaries, zeros, small values)
    let interesting: Vec<(i32,i32,i32,i32,i32,i32)> = vec![
        (0, 0, 0, 0, 0, 0),
        (100, 100, 100, 100, 100, 100),
        (0, 0, 100, 100, 50, 50),
        (0, 0, 100, 0, 0, 100),
        (0, 0, 1, 0, 0, 1),
        (50, 50, 50, 50, 50, 50),
        (0, 0, 50, 100, 100, 0),
        (0, 100, 100, 0, 50, 50),
        (1, 0, 0, 1, 0, 0),
        (0, 0, 0, 100, 0, 50),
        (0, 0, 100, 0, 50, 0),
        (10, 20, 30, 40, 50, 60),
        (10, 20, 30, 40, 50, 61),
        (99, 99, 100, 100, 0, 0),
    ];

    // Apply all mutations to interesting seeds
    for &(x0, y0, x1, y1, x2, y2) in &interesting {
        for mk in 0u8..=10 {
            if count >= count_goal { break; }
            let pts = generate_test_case(x0, y0, x1, y1, x2, y2, mk);
            emit(pts, &mut seen, &mut out, &mut count);
        }
        if count >= count_goal { break; }
    }

    // Random test cases with random mutations
    while count < count_goal {
        let x0 = rng.gen_range_i64(0, 100) as i32;
        let y0 = rng.gen_range_i64(0, 100) as i32;
        let x1 = rng.gen_range_i64(0, 100) as i32;
        let y1 = rng.gen_range_i64(0, 100) as i32;
        let x2 = rng.gen_range_i64(0, 100) as i32;
        let y2 = rng.gen_range_i64(0, 100) as i32;
        let mk = rng.gen_range_usize(0, 10) as u8;
        let pts = generate_test_case(x0, y0, x1, y1, x2, y2, mk);
        emit(pts, &mut seen, &mut out, &mut count);
    }
}
