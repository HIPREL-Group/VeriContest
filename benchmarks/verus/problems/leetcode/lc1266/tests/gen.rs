use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    xs: &Vec<i32>,
    ys: &Vec<i32>,
    mutation_kind: u8,
) -> (result: Vec<Vec<i32>>)
    requires
        1 <= xs.len() <= 100,
        xs.len() == ys.len(),
        forall|i: int| 0 <= i < xs.len() ==> -1000 <= #[trigger] xs[i] <= 1000,
        forall|i: int| 0 <= i < ys.len() ==> -1000 <= #[trigger] ys[i] <= 1000,
    ensures
        1 <= result.len() <= 100,
        forall|i: int| 0 <= i < result.len() ==>
            (#[trigger] result[i]).len() == 2
            && -1000 <= result[i][0] <= 1000
            && -1000 <= result[i][1] <= 1000,
{
    let n = xs.len();
    let mut points: Vec<Vec<i32>> = Vec::new();
    let mut k: usize = 0;
    while k < n
        invariant
            n == xs.len(),
            n == ys.len(),
            1 <= n <= 100,
            0 <= k <= n,
            points.len() == k,
            forall|i: int| 0 <= i < xs.len() ==> -1000 <= #[trigger] xs[i] <= 1000,
            forall|i: int| 0 <= i < ys.len() ==> -1000 <= #[trigger] ys[i] <= 1000,
            forall|j: int| 0 <= j < k as int ==>
                (#[trigger] points[j]).len() == 2
                && -1000 <= points[j][0] <= 1000
                && -1000 <= points[j][1] <= 1000,
        decreases n - k,
    {
        let mut pt: Vec<i32> = Vec::new();
        pt.push(xs[k]);
        pt.push(ys[k]);
        points.push(pt);
        k += 1;
    }

    if mutation_kind == 0 {
        // identity
        points
    } else if mutation_kind == 1 {
        // set first point to origin [0, 0]
        let mut pts = points;
        let mut origin: Vec<i32> = Vec::new();
        origin.push(0i32);
        origin.push(0i32);
        pts.set(0, origin);
        assert(pts[0int].len() == 2);
        pts
    } else if mutation_kind == 2 {
        // set last point to [1000, 1000]
        let mut pts = points;
        let last = pts.len() - 1;
        let mut corner: Vec<i32> = Vec::new();
        corner.push(1000i32);
        corner.push(1000i32);
        pts.set(last, corner);
        assert(pts[last as int].len() == 2);
        pts
    } else if mutation_kind == 3 {
        // set last point to [-1000, -1000]
        let mut pts = points;
        let last = pts.len() - 1;
        let mut corner: Vec<i32> = Vec::new();
        corner.push(-1000i32);
        corner.push(-1000i32);
        pts.set(last, corner);
        assert(pts[last as int].len() == 2);
        pts
    } else if mutation_kind == 4 && points.len() < 100 {
        // append origin point (grow)
        let mut pts = points;
        let mut origin: Vec<i32> = Vec::new();
        origin.push(0i32);
        origin.push(0i32);
        pts.push(origin);
        pts
    } else if mutation_kind == 5 && points.len() > 1 {
        // remove last point (shrink)
        let mut pts = points;
        pts.pop();
        pts
    } else if mutation_kind == 6 && points[0][0] < 1000 {
        // nudge first point x up
        let mut pts = points;
        let new_x = pts[0][0] + 1;
        let old_y = pts[0][1];
        let mut new_pt: Vec<i32> = Vec::new();
        new_pt.push(new_x);
        new_pt.push(old_y);
        pts.set(0, new_pt);
        assert(pts[0int].len() == 2);
        pts
    } else if mutation_kind == 7 && points[0][1] < 1000 {
        // nudge first point y up
        let mut pts = points;
        let old_x = pts[0][0];
        let new_y = pts[0][1] + 1;
        let mut new_pt: Vec<i32> = Vec::new();
        new_pt.push(old_x);
        new_pt.push(new_y);
        pts.set(0, new_pt);
        assert(pts[0int].len() == 2);
        pts
    } else {
        // fallback: identity
        points
    }
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

extern crate serde_json;
use serde_json::json;

fn random_points(rng: &mut Rng, n: usize) -> (Vec<i32>, Vec<i32>) {
    let mut xs = Vec::with_capacity(n);
    let mut ys = Vec::with_capacity(n);
    for _ in 0..n {
        xs.push(rng.gen_range_i64(-1000, 1000) as i32);
        ys.push(rng.gen_range_i64(-1000, 1000) as i32);
    }
    (xs, ys)
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1266);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |points: Vec<Vec<i32>>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target {
            return;
        }
        let key = format!("{:?}", points);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::min_time_to_visit_all_points(points.clone());
        writeln!(out, "{}", json!({"input": {"points": points}, "output": output})).unwrap();
        *count += 1;
    };

    // Example test cases from description.md
    let example_seeds: Vec<(Vec<i32>, Vec<i32>)> = vec![
        (vec![1, 3, -1], vec![1, 4, 0]),       // Example 1: [[1,1],[3,4],[-1,0]] -> 7
        (vec![3, -2], vec![2, 2]),              // Example 2: [[3,2],[-2,2]] -> 5
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7];

    // Apply every mutation to example seeds
    for (xs, ys) in &example_seeds {
        for &mk in &mutation_kinds {
            if count >= target { break; }
            let result = generate_test_case(xs, ys, mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Interesting hand-crafted seeds
    let hand_seeds: Vec<(Vec<i32>, Vec<i32>)> = vec![
        (vec![0], vec![0]),                             // single point
        (vec![0, 0], vec![0, 0]),                       // same point twice
        (vec![-1000, 1000], vec![-1000, 1000]),          // extreme corners
        (vec![1000, -1000], vec![1000, -1000]),          // opposite extreme corners
        (vec![0, 1000, -1000, 0], vec![0, -1000, 1000, 0]),  // zig-zag extremes
        (vec![0, 1, 2, 3, 4], vec![0, 1, 2, 3, 4]),    // diagonal line
        (vec![0, 0, 0, 0, 0], vec![0, 1, 2, 3, 4]),    // vertical line
        (vec![0, 1, 2, 3, 4], vec![0, 0, 0, 0, 0]),    // horizontal line
        (vec![-1000], vec![-1000]),                      // single extreme point
        (vec![1000], vec![1000]),                        // single extreme point
    ];

    for (xs, ys) in &hand_seeds {
        for &mk in &mutation_kinds {
            if count >= target { break; }
            let result = generate_test_case(xs, ys, mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds with diverse sizes
    while count < target {
        let n = match count % 5 {
            0 => rng.gen_range_usize(1, 3),      // tiny
            1 => rng.gen_range_usize(1, 10),     // small
            2 => rng.gen_range_usize(11, 30),    // medium
            3 => rng.gen_range_usize(31, 70),    // large
            _ => rng.gen_range_usize(71, 100),   // max
        };
        let (xs, ys) = random_points(&mut rng, n);
        let mk = rng.gen_range_usize(0, 7) as u8;
        let result = generate_test_case(&xs, &ys, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }
}
