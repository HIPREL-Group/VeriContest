use vstd::prelude::*;

verus! {

pub open spec fn valid_pt(p: Seq<i32>) -> bool {
    p.len() == 2 && 1 <= p[0] && p[0] <= 10000 && 1 <= p[1] && p[1] <= 10000
}

pub fn generate_test_case(
    x: i32,
    y: i32,
    xs: Vec<i32>,
    ys: Vec<i32>,
    mutation_kind: u8,
) -> (result: (i32, i32, Vec<Vec<i32>>))
    requires
        1 <= x <= 10000,
        1 <= y <= 10000,
        1 <= xs.len() <= 10000,
        xs.len() == ys.len(),
        forall|i: int| 0 <= i < xs.len() ==> 1 <= #[trigger] xs[i] <= 10000,
        forall|i: int| 0 <= i < ys.len() ==> 1 <= #[trigger] ys[i] <= 10000,
    ensures
        1 <= result.2.len() <= 10000,
        forall|i: int| #![trigger valid_pt(result.2[i]@)] 0 <= i < result.2.len() ==> valid_pt(result.2[i]@),
        1 <= result.0 <= 10000,
        1 <= result.1 <= 10000,
{
    let mut xs = xs;
    let mut ys = ys;
    let n = xs.len();

    // Apply coordinate mutations before building points
    if mutation_kind == 1 {
        // First point shares x with query
        xs.set(0, x);
    } else if mutation_kind == 2 {
        // First point shares y with query
        ys.set(0, y);
    } else if mutation_kind == 3 {
        // First point is exact query location
        xs.set(0, x);
        ys.set(0, y);
    } else if mutation_kind == 4 {
        // Last point shares x with query
        let last = xs.len() - 1;
        xs.set(last, x);
    } else if mutation_kind == 5 {
        // Last point shares y with query
        let last = ys.len() - 1;
        ys.set(last, y);
    }

    // Build Vec<Vec<i32>> from coordinate arrays
    let mut points: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == xs.len(),
            n == ys.len(),
            1 <= n <= 10000,
            points.len() == i,
            forall|k: int| 0 <= k < xs.len() ==> 1 <= #[trigger] xs[k] <= 10000,
            forall|k: int| 0 <= k < ys.len() ==> 1 <= #[trigger] ys[k] <= 10000,
            forall|k: int| #![trigger valid_pt(points[k]@)] 0 <= k < i as int ==> valid_pt(points[k]@),
        decreases n - i,
    {
        let mut pt: Vec<i32> = Vec::new();
        pt.push(xs[i]);
        pt.push(ys[i]);
        assert(pt@.len() == 2);
        assert(1 <= pt[0] && pt[0] <= 10000);
        assert(1 <= pt[1] && pt[1] <= 10000);
        assert(valid_pt(pt@));
        points.push(pt);
        i += 1;
    }

    (x, y, points)
}

} // verus!

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

extern crate serde_json;
use serde_json::json;

fn random_coords(rng: &mut Rng, n: usize) -> (Vec<i32>, Vec<i32>) {
    let mut xs = Vec::with_capacity(n);
    let mut ys = Vec::with_capacity(n);
    for _ in 0..n {
        xs.push(rng.gen_range_i64(1, 10000) as i32);
        ys.push(rng.gen_range_i64(1, 10000) as i32);
    }
    (xs, ys)
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1779);
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    macro_rules! emit {
        ($x:expr, $y:expr, $xs:expr, $ys:expr, $mk:expr) => {
            if count < goal {
                let xs_val: Vec<i32> = $xs;
                let ys_val: Vec<i32> = $ys;
                let (rx, ry, points) = generate_test_case($x, $y, xs_val, ys_val, $mk);
                let result = Solution::nearest_valid_point(rx, ry, points.clone());
                let line = json!({
                    "input": {"x": rx, "y": ry, "points": points},
                    "output": result
                }).to_string();
                if seen.insert(line.clone()) {
                    writeln!(out, "{}", line).unwrap();
                    count += 1;
                }
            }
        };
    }

    // ---- LeetCode examples ----
    // Example 1: x=3, y=4, points=[[1,2],[3,1],[2,4],[2,3],[4,4]] -> 2
    emit!(3, 4, vec![1, 3, 2, 2, 4], vec![2, 1, 4, 3, 4], 0);
    // Example 2: x=3, y=4, points=[[3,4]] -> 0
    emit!(3, 4, vec![3], vec![4], 0);
    // Example 3: x=3, y=4, points=[[2,3]] -> -1
    emit!(3, 4, vec![2], vec![3], 0);

    // ---- Systematic mutations on seed inputs ----
    let seed_cases: Vec<(i32, i32, Vec<i32>, Vec<i32>)> = vec![
        (3, 4, vec![1, 3, 2, 2, 4], vec![2, 1, 4, 3, 4]),
        (1, 1, vec![1], vec![1]),
        (10000, 10000, vec![10000], vec![10000]),
        (5000, 5000, vec![1, 10000, 5000], vec![10000, 1, 5000]),
        (1, 10000, vec![2, 3, 4], vec![9999, 9998, 9997]),
        (10000, 1, vec![9999, 9998, 9997], vec![2, 3, 4]),
        (1, 1, vec![2, 3], vec![2, 3]),
        (5000, 5000, vec![5000], vec![5000]),
    ];

    for (x, y, xs, ys) in &seed_cases {
        for mk in 0u8..=5 {
            emit!(*x, *y, xs.clone(), ys.clone(), mk);
        }
    }

    // ---- Random test cases with size classes ----
    while count < goal {
        let n = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 3),       // tiny
            1 => rng.gen_range_usize(1, 10),       // small
            2 => rng.gen_range_usize(11, 100),     // medium
            3 => rng.gen_range_usize(101, 1000),   // large
            _ => rng.gen_range_usize(1001, 10000), // max
        };
        let (xs, ys) = random_coords(&mut rng, n);

        // Mix in boundary values for x and y ~20% of the time
        let x = if rng.gen_range_usize(0, 4) == 0 {
            match rng.gen_range_usize(0, 2) {
                0 => 1i32,
                1 => 10000,
                _ => 5000,
            }
        } else {
            rng.gen_range_i64(1, 10000) as i32
        };
        let y = if rng.gen_range_usize(0, 4) == 0 {
            match rng.gen_range_usize(0, 2) {
                0 => 1i32,
                1 => 10000,
                _ => 5000,
            }
        } else {
            rng.gen_range_i64(1, 10000) as i32
        };

        let mk = rng.gen_range_usize(0, 5) as u8;
        emit!(x, y, xs, ys, mk);
    }
}
