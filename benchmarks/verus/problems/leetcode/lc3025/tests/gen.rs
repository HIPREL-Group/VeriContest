use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    xs: &Vec<i32>,
    ys: &Vec<i32>,
    mutation_kind: u8,
) -> (result: Vec<Vec<i32>>)
    requires
        xs.len() == ys.len(),
        2 <= xs.len() <= 50,
        forall|i: int| 0 <= i < xs.len() ==> 0 <= #[trigger] xs[i] <= 50,
        forall|i: int| 0 <= i < ys.len() ==> 0 <= #[trigger] ys[i] <= 50,
        forall|i: int, j: int| 0 <= i < j < xs.len()
            ==> (#[trigger] xs[i] != #[trigger] xs[j] || ys[i] != ys[j]),
    ensures
        2 <= result.len() <= 50,
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i].len() == 2,
        forall|i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i][0] <= 50,
        forall|i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i][1] <= 50,
        forall|i: int, j: int| 0 <= i < j < result.len()
            ==> #[trigger] result[i] != #[trigger] result[j],
{
    let n: usize = if mutation_kind == 1 && xs.len() > 2 {
        xs.len() - 1
    } else {
        xs.len()
    };

    let mut points: Vec<Vec<i32>> = Vec::new();
    let mut k: usize = 0;
    while k < n
        invariant
            xs.len() == ys.len(),
            2 <= xs.len() <= 50,
            2 <= n <= xs.len(),
            0 <= k <= n,
            points.len() == k,
            forall|i: int| 0 <= i < xs.len() ==> 0 <= #[trigger] xs[i] <= 50,
            forall|i: int| 0 <= i < ys.len() ==> 0 <= #[trigger] ys[i] <= 50,
            forall|i: int, j: int| 0 <= i < j < xs.len()
                ==> (#[trigger] xs[i] != #[trigger] xs[j] || ys[i] != ys[j]),
            forall|i: int| 0 <= i < k as int ==> #[trigger] points[i].len() == 2,
            forall|i: int| 0 <= i < k as int ==> points[i][0] == xs[i],
            forall|i: int| 0 <= i < k as int ==> points[i][1] == ys[i],
            forall|i: int| 0 <= i < k as int ==> 0 <= #[trigger] points[i][0] <= 50,
            forall|i: int| 0 <= i < k as int ==> 0 <= #[trigger] points[i][1] <= 50,
            forall|i: int, j: int| 0 <= i < j < k as int
                ==> #[trigger] points[i] != #[trigger] points[j],
        decreases n - k,
    {
        let mut pt: Vec<i32> = Vec::new();
        pt.push(xs[k]);
        pt.push(ys[k]);

        proof {
            assert forall|i: int| 0 <= i < k as int implies points[i] != pt by {
                // From the invariant: points[i][0] == xs[i], points[i][1] == ys[i]
                // From construction: pt[0] == xs[k], pt[1] == ys[k]
                // From requires: i < k < n <= xs.len(), so xs[i] != xs[k] || ys[i] != ys[k]
                assert(points@[i]@[0] == xs@[i]);
                assert(pt@[0] == xs@[k as int]);
                assert(points@[i]@[1] == ys@[i]);
                assert(pt@[1] == ys@[k as int]);
                if xs@[i] == xs@[k as int] {
                    assert(ys@[i] != ys@[k as int]);
                    assert(points@[i]@[1] != pt@[1]);
                }
            };
        }

        points.push(pt);
        k += 1;
    }

    points
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
        assert!(lo <= hi);
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

struct Solution;
include!("../code.rs");

fn build_points(xs: &Vec<i32>, ys: &Vec<i32>, mutation_kind: u8) -> Vec<Vec<i32>> {
    generate_test_case(xs, ys, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_distinct_points(rng: &mut Rng, n: usize) -> (Vec<i32>, Vec<i32>) {
    use std::collections::HashSet;
    let mut used = HashSet::new();
    let mut xs = Vec::with_capacity(n);
    let mut ys = Vec::with_capacity(n);
    while xs.len() < n {
        let x = rng.gen_range_usize(0, 50) as i32;
        let y = rng.gen_range_usize(0, 50) as i32;
        if used.insert((x, y)) {
            xs.push(x);
            ys.push(y);
        }
    }
    (xs, ys)
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(3025);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);
    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut total = 0usize;

    let mut emit = |points: Vec<Vec<i32>>,
                    seen: &mut HashSet<String>,
                    out: &mut std::io::BufWriter<std::fs::File>,
                    total: &mut usize| {
        if *total >= count {
            return;
        }
        let key = format!("{:?}", points);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::number_of_pairs(points.clone());
        writeln!(
            out,
            "{}",
            json!({"input": {"points": points}, "output": output})
        )
        .unwrap();
        *total += 1;
    };

    // Example test cases from description.md
    let examples: Vec<(Vec<i32>, Vec<i32>)> = vec![
        (vec![1, 2, 3], vec![1, 2, 3]),       // [[1,1],[2,2],[3,3]] -> 0
        (vec![6, 4, 2], vec![2, 4, 6]),       // [[6,2],[4,4],[2,6]] -> 2
        (vec![3, 1, 1], vec![1, 3, 1]),       // [[3,1],[1,3],[1,1]] -> 2
    ];
    for (xs, ys) in &examples {
        let points = build_points(xs, ys, 0);
        emit(points, &mut seen, &mut out, &mut total);
    }

    // Size classes with both mutation kinds
    let sizes: Vec<usize> = vec![2, 3, 5, 10, 20, 30, 40, 50];
    for &sz in &sizes {
        for mk in 0u8..2 {
            if mk == 1 && sz <= 2 {
                continue;
            }
            let (xs, ys) = random_distinct_points(&mut rng, sz);
            let points = build_points(&xs, &ys, mk);
            emit(points, &mut seen, &mut out, &mut total);
        }
    }

    // Boundary/special cases: all points on a vertical line (same x)
    {
        let n = 10;
        let xs: Vec<i32> = vec![25; n];
        let ys: Vec<i32> = (0..n as i32).collect();
        let points = build_points(&xs, &ys, 0);
        emit(points, &mut seen, &mut out, &mut total);
    }
    // All points on a horizontal line (same y)
    {
        let n = 10;
        let xs: Vec<i32> = (0..n as i32).collect();
        let ys: Vec<i32> = vec![25; n];
        let points = build_points(&xs, &ys, 0);
        emit(points, &mut seen, &mut out, &mut total);
    }
    // Diagonal points
    {
        let n = 10;
        let xs: Vec<i32> = (0..n as i32).collect();
        let ys: Vec<i32> = (0..n as i32).collect();
        let points = build_points(&xs, &ys, 0);
        emit(points, &mut seen, &mut out, &mut total);
    }
    // Corner points
    {
        let xs = vec![0, 50, 0, 50];
        let ys = vec![0, 0, 50, 50];
        let points = build_points(&xs, &ys, 0);
        emit(points, &mut seen, &mut out, &mut total);
    }
    // Min size (2 points)
    {
        let xs = vec![0, 50];
        let ys = vec![0, 50];
        let points = build_points(&xs, &ys, 0);
        emit(points, &mut seen, &mut out, &mut total);
    }
    // Min size: upper-left relationship
    {
        let xs = vec![0, 50];
        let ys = vec![50, 0];
        let points = build_points(&xs, &ys, 0);
        emit(points, &mut seen, &mut out, &mut total);
    }
    // Max size (50 distinct points)
    {
        let (xs, ys) = random_distinct_points(&mut rng, 50);
        let points = build_points(&xs, &ys, 0);
        emit(points, &mut seen, &mut out, &mut total);
    }

    // Fill remaining with random inputs
    while total < count {
        let sz = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(2, 5),
            1 => rng.gen_range_usize(2, 10),
            2 => rng.gen_range_usize(11, 30),
            _ => rng.gen_range_usize(31, 50),
        };
        let mk = rng.gen_range_usize(0, 1) as u8;
        if mk == 1 && sz <= 2 {
            continue;
        }
        let (xs, ys) = random_distinct_points(&mut rng, sz);
        let points = build_points(&xs, &ys, mk);
        emit(points, &mut seen, &mut out, &mut total);
    }
}
