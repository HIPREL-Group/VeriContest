use vstd::prelude::*;

verus! {

/// Generates two valid rectangles (rec1, rec2) from construction parameters.
/// Each rectangle is [x1, y1, x2, y2] with x2 > x1 and y2 > y1.
pub fn generate_test_case(
    x1_a: i32, y1_a: i32, w_a: i32,  h_a: i32,
    x1_b: i32, y1_b: i32, w_b: i32,  h_b: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        -1_000_000_000 <= x1_a <= 999_999_999,
        -1_000_000_000 <= y1_a <= 999_999_999,
        1 <= w_a <= 1_000_000_000 - x1_a,
        1 <= h_a <= 1_000_000_000 - y1_a,
        -1_000_000_000 <= x1_b <= 999_999_999,
        -1_000_000_000 <= y1_b <= 999_999_999,
        1 <= w_b <= 1_000_000_000 - x1_b,
        1 <= h_b <= 1_000_000_000 - y1_b,
    ensures
        result.0.len() == 4,
        result.1.len() == 4,
        forall|i: int| 0 <= i < result.0.len()
            ==> -1_000_000_000 <= #[trigger] result.0[i] <= 1_000_000_000,
        forall|i: int| 0 <= i < result.1.len()
            ==> -1_000_000_000 <= #[trigger] result.1[i] <= 1_000_000_000,
        result.0[2] > result.0[0],
        result.0[3] > result.0[1],
        result.1[2] > result.1[0],
        result.1[3] > result.1[1],
{
    let x2_a: i32 = x1_a + w_a;
    let y2_a: i32 = y1_a + h_a;
    let x2_b: i32 = x1_b + w_b;
    let y2_b: i32 = y1_b + h_b;

    if mutation_kind == 0 {
        // identity: build rectangles directly
        let mut rec1 = Vec::new();
        rec1.push(x1_a); rec1.push(y1_a); rec1.push(x2_a); rec1.push(y2_a);
        let mut rec2 = Vec::new();
        rec2.push(x1_b); rec2.push(y1_b); rec2.push(x2_b); rec2.push(y2_b);
        assert(rec1[0] == x1_a);
        assert(rec1[1] == y1_a);
        assert(rec1[2] == x2_a);
        assert(rec1[3] == y2_a);
        assert(rec2[0] == x1_b);
        assert(rec2[1] == y1_b);
        assert(rec2[2] == x2_b);
        assert(rec2[3] == y2_b);
        (rec1, rec2)
    } else if mutation_kind == 1 {
        // swap: exchange rec1 and rec2
        let mut rec1 = Vec::new();
        rec1.push(x1_b); rec1.push(y1_b); rec1.push(x2_b); rec1.push(y2_b);
        let mut rec2 = Vec::new();
        rec2.push(x1_a); rec2.push(y1_a); rec2.push(x2_a); rec2.push(y2_a);
        assert(rec1[0] == x1_b);
        assert(rec1[1] == y1_b);
        assert(rec1[2] == x2_b);
        assert(rec1[3] == y2_b);
        assert(rec2[0] == x1_a);
        assert(rec2[1] == y1_a);
        assert(rec2[2] == x2_a);
        assert(rec2[3] == y2_a);
        (rec1, rec2)
    } else if mutation_kind == 2 {
        // nudge rec1 x1 up by 1 if space allows (shrink width)
        let nx1 = if w_a > 1 { (x1_a + 1) as i32 } else { x1_a };
        let mut rec1 = Vec::new();
        rec1.push(nx1); rec1.push(y1_a); rec1.push(x2_a); rec1.push(y2_a);
        let mut rec2 = Vec::new();
        rec2.push(x1_b); rec2.push(y1_b); rec2.push(x2_b); rec2.push(y2_b);
        assert(rec1[0] == nx1);
        assert(rec1[1] == y1_a);
        assert(rec1[2] == x2_a);
        assert(rec1[3] == y2_a);
        assert(rec2[0] == x1_b);
        assert(rec2[1] == y1_b);
        assert(rec2[2] == x2_b);
        assert(rec2[3] == y2_b);
        (rec1, rec2)
    } else if mutation_kind == 3 {
        // nudge rec2 y1 up by 1 if space allows (shrink height)
        let ny1 = if h_b > 1 { (y1_b + 1) as i32 } else { y1_b };
        let mut rec1 = Vec::new();
        rec1.push(x1_a); rec1.push(y1_a); rec1.push(x2_a); rec1.push(y2_a);
        let mut rec2 = Vec::new();
        rec2.push(x1_b); rec2.push(ny1); rec2.push(x2_b); rec2.push(y2_b);
        assert(rec1[0] == x1_a);
        assert(rec1[1] == y1_a);
        assert(rec1[2] == x2_a);
        assert(rec1[3] == y2_a);
        assert(rec2[0] == x1_b);
        assert(rec2[1] == ny1);
        assert(rec2[2] == x2_b);
        assert(rec2[3] == y2_b);
        (rec1, rec2)
    } else if mutation_kind == 4 {
        // make rec2 == rec1 (identical rectangles, always overlap)
        let mut rec1 = Vec::new();
        rec1.push(x1_a); rec1.push(y1_a); rec1.push(x2_a); rec1.push(y2_a);
        let mut rec2 = Vec::new();
        rec2.push(x1_a); rec2.push(y1_a); rec2.push(x2_a); rec2.push(y2_a);
        assert(rec1[0] == x1_a);
        assert(rec1[1] == y1_a);
        assert(rec1[2] == x2_a);
        assert(rec1[3] == y2_a);
        assert(rec2[0] == x1_a);
        assert(rec2[1] == y1_a);
        assert(rec2[2] == x2_a);
        assert(rec2[3] == y2_a);
        (rec1, rec2)
    } else if mutation_kind == 5 {
        // place rec2 to the right of rec1 (no overlap in x)
        // rec2.x1 = rec1.x2, so they share an edge but don't overlap
        let nx1_b = x2_a;
        let nx2_b = if nx1_b < 1_000_000_000 { (nx1_b + 1) as i32 } else { nx1_b };
        // only valid if nx2_b > nx1_b
        if nx2_b > nx1_b {
            let mut rec1 = Vec::new();
            rec1.push(x1_a); rec1.push(y1_a); rec1.push(x2_a); rec1.push(y2_a);
            let mut rec2 = Vec::new();
            rec2.push(nx1_b); rec2.push(y1_b); rec2.push(nx2_b); rec2.push(y2_b);
            assert(rec1[0] == x1_a);
            assert(rec1[1] == y1_a);
            assert(rec1[2] == x2_a);
            assert(rec1[3] == y2_a);
            assert(rec2[0] == nx1_b);
            assert(rec2[1] == y1_b);
            assert(rec2[2] == nx2_b);
            assert(rec2[3] == y2_b);
            (rec1, rec2)
        } else {
            // fallback
            let mut rec1 = Vec::new();
            rec1.push(x1_a); rec1.push(y1_a); rec1.push(x2_a); rec1.push(y2_a);
            let mut rec2 = Vec::new();
            rec2.push(x1_b); rec2.push(y1_b); rec2.push(x2_b); rec2.push(y2_b);
            assert(rec1[0] == x1_a);
            assert(rec1[1] == y1_a);
            assert(rec1[2] == x2_a);
            assert(rec1[3] == y2_a);
            assert(rec2[0] == x1_b);
            assert(rec2[1] == y1_b);
            assert(rec2[2] == x2_b);
            assert(rec2[3] == y2_b);
            (rec1, rec2)
        }
    } else if mutation_kind == 6 {
        // place rec2 above rec1 (no overlap in y)
        let ny1_b = y2_a;
        let ny2_b = if ny1_b < 1_000_000_000 { (ny1_b + 1) as i32 } else { ny1_b };
        if ny2_b > ny1_b {
            let mut rec1 = Vec::new();
            rec1.push(x1_a); rec1.push(y1_a); rec1.push(x2_a); rec1.push(y2_a);
            let mut rec2 = Vec::new();
            rec2.push(x1_b); rec2.push(ny1_b); rec2.push(x2_b); rec2.push(ny2_b);
            assert(rec1[0] == x1_a);
            assert(rec1[1] == y1_a);
            assert(rec1[2] == x2_a);
            assert(rec1[3] == y2_a);
            assert(rec2[0] == x1_b);
            assert(rec2[1] == ny1_b);
            assert(rec2[2] == x2_b);
            assert(rec2[3] == ny2_b);
            (rec1, rec2)
        } else {
            let mut rec1 = Vec::new();
            rec1.push(x1_a); rec1.push(y1_a); rec1.push(x2_a); rec1.push(y2_a);
            let mut rec2 = Vec::new();
            rec2.push(x1_b); rec2.push(y1_b); rec2.push(x2_b); rec2.push(y2_b);
            assert(rec1[0] == x1_a);
            assert(rec1[1] == y1_a);
            assert(rec1[2] == x2_a);
            assert(rec1[3] == y2_a);
            assert(rec2[0] == x1_b);
            assert(rec2[1] == y1_b);
            assert(rec2[2] == x2_b);
            assert(rec2[3] == y2_b);
            (rec1, rec2)
        }
    } else if mutation_kind == 7 {
        // halve widths (both rects get narrower)
        let hw_a = if w_a / 2 >= 1 { w_a / 2 } else { 1 };
        let hw_b = if w_b / 2 >= 1 { w_b / 2 } else { 1 };
        let nx2_a = x1_a + hw_a;
        let nx2_b = x1_b + hw_b;
        let mut rec1 = Vec::new();
        rec1.push(x1_a); rec1.push(y1_a); rec1.push(nx2_a); rec1.push(y2_a);
        let mut rec2 = Vec::new();
        rec2.push(x1_b); rec2.push(y1_b); rec2.push(nx2_b); rec2.push(y2_b);
        assert(rec1[0] == x1_a);
        assert(rec1[1] == y1_a);
        assert(rec1[2] == nx2_a);
        assert(rec1[3] == y2_a);
        assert(rec2[0] == x1_b);
        assert(rec2[1] == y1_b);
        assert(rec2[2] == nx2_b);
        assert(rec2[3] == y2_b);
        (rec1, rec2)
    } else if mutation_kind == 8 {
        // zero-origin: set x1=0, y1=0 for rec1
        let nx2_a = if w_a <= 1_000_000_000 { w_a } else { 1_000_000_000i32 };
        let ny2_a = if h_a <= 1_000_000_000 { h_a } else { 1_000_000_000i32 };
        let mut rec1 = Vec::new();
        rec1.push(0i32); rec1.push(0i32); rec1.push(nx2_a); rec1.push(ny2_a);
        let mut rec2 = Vec::new();
        rec2.push(x1_b); rec2.push(y1_b); rec2.push(x2_b); rec2.push(y2_b);
        assert(rec1[0] == 0i32);
        assert(rec1[1] == 0i32);
        assert(rec1[2] == nx2_a);
        assert(rec1[3] == ny2_a);
        assert(rec2[0] == x1_b);
        assert(rec2[1] == y1_b);
        assert(rec2[2] == x2_b);
        assert(rec2[3] == y2_b);
        (rec1, rec2)
    } else {
        // fallback: identity
        let mut rec1 = Vec::new();
        rec1.push(x1_a); rec1.push(y1_a); rec1.push(x2_a); rec1.push(y2_a);
        let mut rec2 = Vec::new();
        rec2.push(x1_b); rec2.push(y1_b); rec2.push(x2_b); rec2.push(y2_b);
        assert(rec1[0] == x1_a);
        assert(rec1[1] == y1_a);
        assert(rec1[2] == x2_a);
        assert(rec1[3] == y2_a);
        assert(rec2[0] == x1_b);
        assert(rec2[1] == y1_b);
        assert(rec2[2] == x2_b);
        assert(rec2[3] == y2_b);
        (rec1, rec2)
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

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        self.gen_range_i64(lo as i64, hi as i64) as i32
    }
}

struct Solution;
include!("../code.rs");

fn gen_rect_params(rng: &mut Rng) -> (i32, i32, i32, i32) {
    let x1 = rng.gen_range_i32(-1_000_000_000, 999_999_999);
    let y1 = rng.gen_range_i32(-1_000_000_000, 999_999_999);
    let max_w = 1_000_000_000 - x1;
    let max_h = 1_000_000_000 - y1;
    let w = rng.gen_range_i32(1, max_w);
    let h = rng.gen_range_i32(1, max_h);
    (x1, y1, w, h)
}

fn main() {
    use std::io::Write;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);

    let mut rng = Rng::new(seed);
    let mut written = 0usize;

    // Example inputs from description.md
    let examples: Vec<(Vec<i32>, Vec<i32>)> = vec![
        (vec![0, 0, 2, 2], vec![1, 1, 3, 3]),
        (vec![0, 0, 1, 1], vec![1, 0, 2, 1]),
        (vec![0, 0, 1, 1], vec![2, 2, 3, 3]),
    ];

    for (rec1, rec2) in &examples {
        let result = Solution::is_rectangle_overlap(rec1.clone(), rec2.clone());
        writeln!(out, "{}", json!({
            "input": {"rec1": rec1, "rec2": rec2},
            "output": result
        })).unwrap();
        written += 1;
    }

    // Boundary test cases
    let boundary_cases: Vec<(Vec<i32>, Vec<i32>)> = vec![
        // touching at corner
        (vec![0, 0, 1, 1], vec![1, 1, 2, 2]),
        // touching at edge
        (vec![0, 0, 2, 2], vec![2, 0, 4, 2]),
        // one inside another
        (vec![-10, -10, 10, 10], vec![-5, -5, 5, 5]),
        // large coords, overlapping
        (vec![-1_000_000_000, -1_000_000_000, 0, 0], vec![-1, -1, 1_000_000_000, 1_000_000_000]),
        // large coords, non-overlapping
        (vec![-1_000_000_000, -1_000_000_000, -999_999_999, -999_999_999],
         vec![999_999_999, 999_999_999, 1_000_000_000, 1_000_000_000]),
        // minimal rectangles (width=1, height=1)
        (vec![0, 0, 1, 1], vec![0, 0, 1, 1]),
    ];

    for (rec1, rec2) in &boundary_cases {
        let result = Solution::is_rectangle_overlap(rec1.clone(), rec2.clone());
        writeln!(out, "{}", json!({
            "input": {"rec1": rec1, "rec2": rec2},
            "output": result
        })).unwrap();
        written += 1;
    }

    let num_mutations: u8 = 9;

    // Random test cases with mutations
    while written < count {
        let (x1_a, y1_a, w_a, h_a) = gen_rect_params(&mut rng);
        let (x1_b, y1_b, w_b, h_b) = gen_rect_params(&mut rng);
        let mutation = (written as u8) % (num_mutations + 1);

        let (rec1, rec2) = generate_test_case(
            x1_a, y1_a, w_a, h_a,
            x1_b, y1_b, w_b, h_b,
            mutation,
        );

        let result = Solution::is_rectangle_overlap(rec1.clone(), rec2.clone());
        writeln!(out, "{}", json!({
            "input": {"rec1": rec1, "rec2": rec2},
            "output": result
        })).unwrap();
        written += 1;
    }

    eprintln!("Wrote {} test cases to {:?}", written, out_path);
}
