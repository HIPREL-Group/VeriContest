use vstd::prelude::*;

verus! {

// Generate a pair (lo, hi) with -10_000 <= lo <= hi <= 10_000
// from a base value and a non-negative delta, clamping hi to 10_000.
pub fn generate_pair(base: i32, delta: i32) -> (pair: (i32, i32))
    requires
        -10_000 <= base <= 10_000,
        0 <= delta <= 20_000,
    ensures
        -10_000 <= pair.0 <= pair.1 <= 10_000,
{
    let lo = base;
    let hi = if base + delta > 10_000 { 10_000i32 } else { base + delta };
    (lo, hi)
}

pub fn generate_test_case(
    ax_base: i32, ax_delta: i32,
    ay_base: i32, ay_delta: i32,
    bx_base: i32, bx_delta: i32,
    by_base: i32, by_delta: i32,
    mutation_kind: u8,
) -> (result: (i32, i32, i32, i32, i32, i32, i32, i32))
    requires
        -10_000 <= ax_base <= 10_000,
        0 <= ax_delta <= 20_000,
        -10_000 <= ay_base <= 10_000,
        0 <= ay_delta <= 20_000,
        -10_000 <= bx_base <= 10_000,
        0 <= bx_delta <= 20_000,
        -10_000 <= by_base <= 10_000,
        0 <= by_delta <= 20_000,
    ensures
        -10_000 <= result.0 <= result.2 <= 10_000,
        -10_000 <= result.1 <= result.3 <= 10_000,
        -10_000 <= result.4 <= result.6 <= 10_000,
        -10_000 <= result.5 <= result.7 <= 10_000,
{
    let (ax1, ax2) = generate_pair(ax_base, ax_delta);
    let (ay1, ay2) = generate_pair(ay_base, ay_delta);
    let (bx1, bx2) = generate_pair(bx_base, bx_delta);
    let (by1, by2) = generate_pair(by_base, by_delta);

    if mutation_kind == 0 {
        // identity
        (ax1, ay1, ax2, ay2, bx1, by1, bx2, by2)
    } else if mutation_kind == 1 {
        // zero-area first rectangle (point)
        (ax1, ay1, ax1, ay1, bx1, by1, bx2, by2)
    } else if mutation_kind == 2 {
        // zero-area second rectangle (point)
        (ax1, ay1, ax2, ay2, bx1, by1, bx1, by1)
    } else if mutation_kind == 3 {
        // both rectangles identical
        (ax1, ay1, ax2, ay2, ax1, ay1, ax2, ay2)
    } else if mutation_kind == 4 {
        // swap the two rectangles
        (bx1, by1, bx2, by2, ax1, ay1, ax2, ay2)
    } else if mutation_kind == 5 {
        // first rectangle at origin point
        (0, 0, 0, 0, bx1, by1, bx2, by2)
    } else if mutation_kind == 6 {
        // both zero-area at same point
        (ax1, ay1, ax1, ay1, ax1, ay1, ax1, ay1)
    } else if mutation_kind == 7 {
        // max-area first rectangle
        (-10_000, -10_000, 10_000, 10_000, bx1, by1, bx2, by2)
    } else if mutation_kind == 8 {
        // second rectangle contained inside first (use midpoints)
        let mid_x = if ax1 <= ax2 - 1 { ax1 + 1 } else { ax1 };
        let mid_y = if ay1 <= ay2 - 1 { ay1 + 1 } else { ay1 };
        (ax1, ay1, ax2, ay2, mid_x, mid_y, ax2, ay2)
    } else {
        // fallback: identity
        (ax1, ay1, ax2, ay2, bx1, by1, bx2, by2)
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
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        self.gen_range_i64(lo as i64, hi as i64) as i32
    }
    fn gen_u8(&mut self) -> u8 {
        (self.next_u64() % 256) as u8
    }
}

struct Solution;
include!("../code.rs");

fn main() {
    use std::io::Write;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut count = 0usize;

    // Example 1: ax1=-3, ay1=0, ax2=3, ay2=4, bx1=0, by1=-1, bx2=9, by2=2
    {
        let (ax1, ay1, ax2, ay2, bx1, by1, bx2, by2) = (-3, 0, 3, 4, 0, -1, 9, 2);
        let output = Solution::compute_area(ax1, ay1, ax2, ay2, bx1, by1, bx2, by2);
        writeln!(out, "{}", json!({
            "input": {"ax1": ax1, "ay1": ay1, "ax2": ax2, "ay2": ay2,
                      "bx1": bx1, "by1": by1, "bx2": bx2, "by2": by2},
            "output": output
        })).unwrap();
        count += 1;
    }

    // Example 2: ax1=-2, ay1=-2, ax2=2, ay2=2, bx1=-2, by1=-2, bx2=2, by2=2
    {
        let (ax1, ay1, ax2, ay2, bx1, by1, bx2, by2) = (-2, -2, 2, 2, -2, -2, 2, 2);
        let output = Solution::compute_area(ax1, ay1, ax2, ay2, bx1, by1, bx2, by2);
        writeln!(out, "{}", json!({
            "input": {"ax1": ax1, "ay1": ay1, "ax2": ax2, "ay2": ay2,
                      "bx1": bx1, "by1": by1, "bx2": bx2, "by2": by2},
            "output": output
        })).unwrap();
        count += 1;
    }

    // Boundary values pool
    let boundary: Vec<i32> = vec![-10_000, -1, 0, 1, 10_000, -5_000, 5_000];

    // Generate from boundary combinations with all mutations
    for &b in &boundary {
        for mk in 0..=9u8 {
            if count >= goal { break; }
            let (ax1, ay1, ax2, ay2, bx1, by1, bx2, by2) = generate_test_case(
                b, 0, b, 0, b, 0, b, 0, mk,
            );
            let output = Solution::compute_area(ax1, ay1, ax2, ay2, bx1, by1, bx2, by2);
            writeln!(out, "{}", json!({
                "input": {"ax1": ax1, "ay1": ay1, "ax2": ax2, "ay2": ay2,
                          "bx1": bx1, "by1": by1, "bx2": bx2, "by2": by2},
                "output": output
            })).unwrap();
            count += 1;
        }
        if count >= goal { break; }
    }

    // Random test cases
    while count < goal {
        let ax_base = rng.gen_range_i32(-10_000, 10_000);
        let ax_delta = rng.gen_range_i32(0, 20_000);
        let ay_base = rng.gen_range_i32(-10_000, 10_000);
        let ay_delta = rng.gen_range_i32(0, 20_000);
        let bx_base = rng.gen_range_i32(-10_000, 10_000);
        let bx_delta = rng.gen_range_i32(0, 20_000);
        let by_base = rng.gen_range_i32(-10_000, 10_000);
        let by_delta = rng.gen_range_i32(0, 20_000);
        let mk = rng.gen_u8() % 10;

        let (ax1, ay1, ax2, ay2, bx1, by1, bx2, by2) = generate_test_case(
            ax_base, ax_delta, ay_base, ay_delta,
            bx_base, bx_delta, by_base, by_delta, mk,
        );
        let output = Solution::compute_area(ax1, ay1, ax2, ay2, bx1, by1, bx2, by2);
        writeln!(out, "{}", json!({
            "input": {"ax1": ax1, "ay1": ay1, "ax2": ax2, "ay2": ay2,
                      "bx1": bx1, "by1": by1, "bx2": bx2, "by2": by2},
            "output": output
        })).unwrap();
        count += 1;
    }
}
