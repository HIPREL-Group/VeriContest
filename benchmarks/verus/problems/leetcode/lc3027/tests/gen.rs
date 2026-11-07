use vstd::prelude::*;

verus! {

pub fn generate_test_case(raw: Vec<Vec<i32>>) -> (result: Vec<Vec<i32>>)
    ensures
        2 <= result.len() <= 1000,
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i].len() == 2,
        forall|i: int| 0 <= i < result.len() ==> -1000000000 <= #[trigger] result[i][0] <= 1000000000 && -1000000000 <= result[i][1] <= 1000000000,
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i]@ != result[j]@,
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
{
    let end = if raw.len() > 1000 { 1000usize } else { raw.len() };
    let mut result: Vec<Vec<i32>> = Vec::new();
    let mut i = 0usize;
    while i < end
        invariant
            0 <= i <= end <= raw.len(), end <= 1000, result.len() <= i,
            forall|j: int| 0 <= j < result.len() ==> #[trigger] result[j].len() == 2,
            forall|j: int| 0 <= j < result.len() ==> -1000000000 <= #[trigger] result[j][0] <= 1000000000 && -1000000000 <= result[j][1] <= 1000000000,
            forall|j: int, k: int| 0 <= j < k < result.len() ==> (#[trigger] result[j][0] < #[trigger] result[k][0] || (#[trigger] result[j][0] == #[trigger] result[k][0] && #[trigger] result[j][1] < #[trigger] result[k][1])),
        decreases end - i,
    {
        let x = if raw[i].len() > 0 { raw[i][0] } else { -1000000000 };
        let y = if raw[i].len() > 1 { raw[i][1] } else { -1000000000 };
        let x = if x < -1000000000 { -1000000000 } else if x > 1000000000 { 1000000000 } else { x };
        let y = if y < -1000000000 { -1000000000 } else if y > 1000000000 { 1000000000 } else { y };
        let mut accept = true;
        if result.len() > 0 {
            let last = result.len() - 1;
            assert(result[last as int].len() == 2);
            accept = result[last][0] < x || (result[last][0] == x && result[last][1] < y);
        }
        if accept {
            assert forall|j: int| 0 <= j < result.len() implies
                (result[j][0] < x || (result[j][0] == x && result[j][1] < y)) by {
                if j < result.len() - 1 { assert((result[j][0] < result[result.len() - 1][0] || (result[j][0] == result[result.len() - 1][0] && result[j][1] < result[result.len() - 1][1]))); }
            }
            let mut p = Vec::new();
            p.push(x);
            p.push(y);
            result.push(p);
        }
        i += 1;
    }
    if result.len() < 2 {
        let mut fallback: Vec<Vec<i32>> = Vec::new();
        let mut p = Vec::new();
        p.push(-1000000000);
        p.push(-1000000000);
        fallback.push(p);
        let mut p = Vec::new();
        p.push(-1000000000);
        p.push(-999999999);
        fallback.push(p);
        assert(fallback[0][1] != fallback[1][1]);
        assert(fallback[0]@ != fallback[1]@);
        fallback
    } else {
        assert forall|j: int, k: int| 0 <= j < k < result.len()
            implies result[j]@ != result[k]@ by {
            assert((result[j][0] < result[k][0] || (result[j][0] == result[k][0] && result[j][1] < result[k][1])));
        }
        result
    }
}


pub fn generate_candidate(
    xs: Vec<i32>,
    ys: Vec<i32>,
    mutation_kind: u8,
) -> (points: Vec<Vec<i32>>)
    requires
        2 <= xs.len() <= 1000,
        xs.len() == ys.len(),
        forall |i: int| 0 <= i < xs.len() ==> -1_000_000_000 <= #[trigger] xs[i] <= 1_000_000_000,
        forall |i: int| 0 <= i < ys.len() ==> -1_000_000_000 <= #[trigger] ys[i] <= 1_000_000_000,
    ensures
        2 <= points.len() <= 1000,
        forall |i: int| 0 <= i < points.len() ==> #[trigger] points[i].len() == 2,
        forall |i: int| 0 <= i < points.len()
            ==> -1_000_000_000 <= #[trigger] points[i][0] <= 1_000_000_000
                && -1_000_000_000 <= points[i][1] <= 1_000_000_000,
{
    let n = xs.len();
    let mut points: Vec<Vec<i32>> = Vec::new();

    if mutation_kind == 1 && n > 2 {
        // Shrink: drop the last point, use n-1 points
        let limit = n - 1;
        let mut i: usize = 0;
        while i < limit
            invariant
                2 <= limit <= 1000,
                limit == n - 1,
                n == xs.len(),
                xs.len() == ys.len(),
                0 <= i <= limit,
                points.len() == i as int,
                forall |j: int| 0 <= j < i as int ==> #[trigger] points[j].len() == 2,
                forall |j: int| 0 <= j < i as int
                    ==> -1_000_000_000 <= #[trigger] points[j][0] <= 1_000_000_000
                        && -1_000_000_000 <= points[j][1] <= 1_000_000_000,
                forall |k: int| 0 <= k < xs.len() ==> -1_000_000_000 <= #[trigger] xs[k] <= 1_000_000_000,
                forall |k: int| 0 <= k < ys.len() ==> -1_000_000_000 <= #[trigger] ys[k] <= 1_000_000_000,
            decreases limit - i,
        {
            let mut pt: Vec<i32> = Vec::new();
            pt.push(xs[i]);
            pt.push(ys[i]);
            assert(pt.len() == 2);
            assert(pt[0] == xs[i as int]);
            assert(pt[1] == ys[i as int]);
            points.push(pt);
            i += 1;
        }
        points
    } else if mutation_kind == 2 {
        // Swap x and y coordinates
        let mut i: usize = 0;
        while i < n
            invariant
                2 <= n <= 1000,
                n == xs.len(),
                xs.len() == ys.len(),
                0 <= i <= n,
                points.len() == i as int,
                forall |j: int| 0 <= j < i as int ==> #[trigger] points[j].len() == 2,
                forall |j: int| 0 <= j < i as int
                    ==> -1_000_000_000 <= #[trigger] points[j][0] <= 1_000_000_000
                        && -1_000_000_000 <= points[j][1] <= 1_000_000_000,
                forall |k: int| 0 <= k < xs.len() ==> -1_000_000_000 <= #[trigger] xs[k] <= 1_000_000_000,
                forall |k: int| 0 <= k < ys.len() ==> -1_000_000_000 <= #[trigger] ys[k] <= 1_000_000_000,
            decreases n - i,
        {
            let mut pt: Vec<i32> = Vec::new();
            pt.push(ys[i]);
            pt.push(xs[i]);
            assert(pt.len() == 2);
            assert(pt[0] == ys[i as int]);
            assert(pt[1] == xs[i as int]);
            points.push(pt);
            i += 1;
        }
        points
    } else if mutation_kind == 3 {
        // All x coordinates set to 0
        let mut i: usize = 0;
        while i < n
            invariant
                2 <= n <= 1000,
                n == xs.len(),
                xs.len() == ys.len(),
                0 <= i <= n,
                points.len() == i as int,
                forall |j: int| 0 <= j < i as int ==> #[trigger] points[j].len() == 2,
                forall |j: int| 0 <= j < i as int
                    ==> -1_000_000_000 <= #[trigger] points[j][0] <= 1_000_000_000
                        && -1_000_000_000 <= points[j][1] <= 1_000_000_000,
                forall |k: int| 0 <= k < ys.len() ==> -1_000_000_000 <= #[trigger] ys[k] <= 1_000_000_000,
            decreases n - i,
        {
            let mut pt: Vec<i32> = Vec::new();
            pt.push(0i32);
            pt.push(ys[i]);
            assert(pt.len() == 2);
            assert(pt[0] == 0i32);
            assert(pt[1] == ys[i as int]);
            points.push(pt);
            i += 1;
        }
        points
    } else if mutation_kind == 4 {
        // All y coordinates set to 0
        let mut i: usize = 0;
        while i < n
            invariant
                2 <= n <= 1000,
                n == xs.len(),
                xs.len() == ys.len(),
                0 <= i <= n,
                points.len() == i as int,
                forall |j: int| 0 <= j < i as int ==> #[trigger] points[j].len() == 2,
                forall |j: int| 0 <= j < i as int
                    ==> -1_000_000_000 <= #[trigger] points[j][0] <= 1_000_000_000
                        && -1_000_000_000 <= points[j][1] <= 1_000_000_000,
                forall |k: int| 0 <= k < xs.len() ==> -1_000_000_000 <= #[trigger] xs[k] <= 1_000_000_000,
            decreases n - i,
        {
            let mut pt: Vec<i32> = Vec::new();
            pt.push(xs[i]);
            pt.push(0i32);
            assert(pt.len() == 2);
            assert(pt[0] == xs[i as int]);
            assert(pt[1] == 0i32);
            points.push(pt);
            i += 1;
        }
        points
    } else if mutation_kind == 5 {
        // Negate x coordinates
        let mut i: usize = 0;
        while i < n
            invariant
                2 <= n <= 1000,
                n == xs.len(),
                xs.len() == ys.len(),
                0 <= i <= n,
                points.len() == i as int,
                forall |j: int| 0 <= j < i as int ==> #[trigger] points[j].len() == 2,
                forall |j: int| 0 <= j < i as int
                    ==> -1_000_000_000 <= #[trigger] points[j][0] <= 1_000_000_000
                        && -1_000_000_000 <= points[j][1] <= 1_000_000_000,
                forall |k: int| 0 <= k < xs.len() ==> -1_000_000_000 <= #[trigger] xs[k] <= 1_000_000_000,
                forall |k: int| 0 <= k < ys.len() ==> -1_000_000_000 <= #[trigger] ys[k] <= 1_000_000_000,
            decreases n - i,
        {
            let mut pt: Vec<i32> = Vec::new();
            pt.push(-xs[i]);
            pt.push(ys[i]);
            assert(pt.len() == 2);
            points.push(pt);
            i += 1;
        }
        points
    } else if mutation_kind == 6 {
        // Negate y coordinates
        let mut i: usize = 0;
        while i < n
            invariant
                2 <= n <= 1000,
                n == xs.len(),
                xs.len() == ys.len(),
                0 <= i <= n,
                points.len() == i as int,
                forall |j: int| 0 <= j < i as int ==> #[trigger] points[j].len() == 2,
                forall |j: int| 0 <= j < i as int
                    ==> -1_000_000_000 <= #[trigger] points[j][0] <= 1_000_000_000
                        && -1_000_000_000 <= points[j][1] <= 1_000_000_000,
                forall |k: int| 0 <= k < xs.len() ==> -1_000_000_000 <= #[trigger] xs[k] <= 1_000_000_000,
                forall |k: int| 0 <= k < ys.len() ==> -1_000_000_000 <= #[trigger] ys[k] <= 1_000_000_000,
            decreases n - i,
        {
            let mut pt: Vec<i32> = Vec::new();
            pt.push(xs[i]);
            pt.push(-ys[i]);
            assert(pt.len() == 2);
            points.push(pt);
            i += 1;
        }
        points
    } else if mutation_kind == 7 {
        // Reverse order of points
        let mut i: usize = 0;
        while i < n
            invariant
                2 <= n <= 1000,
                n == xs.len(),
                xs.len() == ys.len(),
                0 <= i <= n,
                points.len() == i as int,
                forall |j: int| 0 <= j < i as int ==> #[trigger] points[j].len() == 2,
                forall |j: int| 0 <= j < i as int
                    ==> -1_000_000_000 <= #[trigger] points[j][0] <= 1_000_000_000
                        && -1_000_000_000 <= points[j][1] <= 1_000_000_000,
                forall |k: int| 0 <= k < xs.len() ==> -1_000_000_000 <= #[trigger] xs[k] <= 1_000_000_000,
                forall |k: int| 0 <= k < ys.len() ==> -1_000_000_000 <= #[trigger] ys[k] <= 1_000_000_000,
            decreases n - i,
        {
            let ri = n - 1 - i;
            let mut pt: Vec<i32> = Vec::new();
            pt.push(xs[ri]);
            pt.push(ys[ri]);
            assert(pt.len() == 2);
            assert(pt[0] == xs[ri as int]);
            assert(pt[1] == ys[ri as int]);
            points.push(pt);
            i += 1;
        }
        points
    } else {
        // Identity: build points[i] = [xs[i], ys[i]]
        let mut i: usize = 0;
        while i < n
            invariant
                2 <= n <= 1000,
                n == xs.len(),
                xs.len() == ys.len(),
                0 <= i <= n,
                points.len() == i as int,
                forall |j: int| 0 <= j < i as int ==> #[trigger] points[j].len() == 2,
                forall |j: int| 0 <= j < i as int
                    ==> -1_000_000_000 <= #[trigger] points[j][0] <= 1_000_000_000
                        && -1_000_000_000 <= points[j][1] <= 1_000_000_000,
                forall |k: int| 0 <= k < xs.len() ==> -1_000_000_000 <= #[trigger] xs[k] <= 1_000_000_000,
                forall |k: int| 0 <= k < ys.len() ==> -1_000_000_000 <= #[trigger] ys[k] <= 1_000_000_000,
            decreases n - i,
        {
            let mut pt: Vec<i32> = Vec::new();
            pt.push(xs[i]);
            pt.push(ys[i]);
            assert(pt.len() == 2);
            assert(pt[0] == xs[i as int]);
            assert(pt[1] == ys[i as int]);
            points.push(pt);
            i += 1;
        }
        points
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
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);

    use std::io::Write;
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);

    // Example test cases from description.md
    let examples: Vec<Vec<Vec<i32>>> = vec![
        vec![vec![1,1], vec![2,2], vec![3,3]],
        vec![vec![6,2], vec![4,4], vec![2,6]],
        vec![vec![3,1], vec![1,3], vec![1,1]],
    ];
    for points in &examples {
        let mut points = points.clone();
        points.sort();
        let points = generate_test_case(points);
        let result = Solution::number_of_pairs(points.clone());
        let pts_json: Vec<Vec<i32>> = points.clone();
        writeln!(out, "{}", json!({
            "input": {"points": pts_json},
            "output": result
        })).unwrap();
    }

    let remaining = if count > examples.len() { count - examples.len() } else { 0 };

    for i in 0..remaining {
        // Size classes
        let n: usize = match i % 5 {
            0 => rng.gen_range_usize(2, 5),       // tiny
            1 => rng.gen_range_usize(2, 10),      // small
            2 => rng.gen_range_usize(11, 50),     // medium
            3 => rng.gen_range_usize(51, 200),    // large
            _ => rng.gen_range_usize(201, 1000),  // max
        };

        // Value range selection
        let (val_lo, val_hi): (i64, i64) = match i % 4 {
            0 => (-1_000_000_000, 1_000_000_000),  // full range
            1 => (-100, 100),                        // small values
            2 => (0, 1_000_000_000),                 // non-negative
            _ => (-1_000_000_000, 0),                // non-positive
        };

        let mut xs: Vec<i32> = Vec::new();
        let mut ys: Vec<i32> = Vec::new();
        for _ in 0..n {
            let x = if i % 10 == 0 {
                // Boundary values
                *[val_lo, val_hi, 0, 1, -1].get(rng.gen_range_usize(0, 4)).unwrap()
            } else {
                rng.gen_range_i64(val_lo, val_hi)
            } as i32;
            let y = if i % 10 == 0 {
                *[val_lo, val_hi, 0, 1, -1].get(rng.gen_range_usize(0, 4)).unwrap()
            } else {
                rng.gen_range_i64(val_lo, val_hi)
            } as i32;
            xs.push(x);
            ys.push(y);
        }

        let mutation_kind: u8 = (i % 8) as u8;
        let points = generate_candidate(xs, ys, mutation_kind);
        let mut points = points.clone();
        points.sort();
        let points = generate_test_case(points);
        let result = Solution::number_of_pairs(points.clone());

        let pts_json: Vec<Vec<i32>> = points.into_iter().map(|p| {
            vec![p[0], p[1]]
        }).collect();

        writeln!(out, "{}", json!({
            "input": {"points": pts_json},
            "output": result
        })).unwrap();
    }
}
