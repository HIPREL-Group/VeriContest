use vstd::prelude::*;

verus! {

pub fn construct_points(raw: Vec<Vec<i32>>) -> (result: Vec<Vec<i32>>)
    ensures
        1 <= result.len() <= 100000,
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i].len() == 2,
        forall|i: int| 0 <= i < result.len() ==> 0 <= (#[trigger] result[i])[0] <= 1000000000 && 0 <= result[i][1] <= 1000000000,
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i]@ != result[j]@,
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
{
    let end = if raw.len() > 100000 { 100000usize } else { raw.len() };
    let mut result: Vec<Vec<i32>> = Vec::new();
    let mut i = 0usize;
    while i < end
        invariant
            0 <= i <= end <= raw.len(), end <= 100000, result.len() <= i,
            forall|j: int| 0 <= j < result.len() ==> #[trigger] result[j].len() == 2,
            forall|j: int| 0 <= j < result.len() ==> 0 <= #[trigger] result[j][0] <= 1000000000 && 0 <= result[j][1] <= 1000000000,
            forall|j: int, k: int| 0 <= j < k < result.len() ==> (#[trigger] result[j][0] < #[trigger] result[k][0] || (#[trigger] result[j][0] == #[trigger] result[k][0] && #[trigger] result[j][1] < #[trigger] result[k][1])),
        decreases end - i,
    {
        let x = if raw[i].len() > 0 { raw[i][0] } else { 0 };
        let y = if raw[i].len() > 1 { raw[i][1] } else { 0 };
        let x = if x < 0 { 0 } else if x > 1000000000 { 1000000000 } else { x };
        let y = if y < 0 { 0 } else if y > 1000000000 { 1000000000 } else { y };
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
    if result.len() < 1 {
        let mut fallback: Vec<Vec<i32>> = Vec::new();
        let mut p = Vec::new();
        p.push(0);
        p.push(0);
        fallback.push(p);

        fallback
    } else {
        assert forall|j: int, k: int| 0 <= j < k < result.len()
            implies result[j]@ != result[k]@ by {
            assert((result[j][0] < result[k][0] || (result[j][0] == result[k][0] && result[j][1] < result[k][1])));
        }
        result
    }
}

pub fn generate_test_case(points: Vec<Vec<i32>>, w: i32) -> (result: (Vec<Vec<i32>>, i32))
    ensures
        1 <= result.0.len() <= 100000,
        forall|i: int| 0 <= i < result.0.len() ==> #[trigger] result.0[i].len() == 2,
        forall|i: int| 0 <= i < result.0.len() ==> 0 <= (#[trigger] result.0[i])[0] <= 1000000000 && 0 <= result.0[i][1] <= 1000000000,
        forall|i: int, j: int| 0 <= i < j < result.0.len() ==> result.0[i]@ != result.0[j]@,
        forall|i: int, j: int| 0 <= i < j < result.0.len() ==> result.0[i] != result.0[j],
        0 <= result.1 <= 1000000000,
{
    (construct_points(points), if w < 0 { 0 } else if w > 1000000000 { 1000000000 } else { w })
}


/// Build a two-element Vec<i32> representing one point [x, y].
fn build_point(x: i32, y: i32) -> (p: Vec<i32>)
    ensures
        p.len() == 2,
        p[0] == x,
        p[1] == y,
{
    let mut p: Vec<i32> = Vec::new();
    p.push(x);
    p.push(y);
    p
}

pub fn generate_candidate(
    xs: &Vec<i32>,
    ys: &Vec<i32>,
    w: i32,
    mutation_kind: u8,
) -> (result: (Vec<Vec<i32>>, i32))
    requires
        xs.len() == ys.len(),
        1 <= xs.len() <= 100000,
        forall|i: int| 0 <= i < xs.len() ==> 0 <= #[trigger] xs[i] <= 1000000000,
        forall|i: int| 0 <= i < ys.len() ==> 0 <= #[trigger] ys[i] <= 1000000000,
        0 <= w <= 1000000000,
    ensures
        1 <= result.0.len() <= 100000,
        forall|i: int| 0 <= i < result.0.len() ==> #[trigger] result.0[i].len() == 2,
        forall|i: int| 0 <= i < result.0.len() ==> 0 <= (#[trigger] result.0[i])[0] <= 1000000000,
        forall|i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i][1] <= 1000000000,
        0 <= result.1 <= 1000000000,
{
    let n: usize = xs.len();
    let mut points: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;

    while i < n
        invariant
            n == xs.len(),
            xs.len() == ys.len(),
            1 <= n <= 100000,
            0 <= i <= n,
            points.len() == i,
            forall|j: int| 0 <= j < i as int ==> #[trigger] points[j].len() == 2,
            forall|j: int| 0 <= j < i as int ==> 0 <= #[trigger] points[j][0] <= 1000000000,
            forall|j: int| 0 <= j < i as int ==> 0 <= #[trigger] points[j][1] <= 1000000000,
            forall|j: int| 0 <= j < xs.len() ==> 0 <= #[trigger] xs[j] <= 1000000000,
            forall|j: int| 0 <= j < ys.len() ==> 0 <= #[trigger] ys[j] <= 1000000000,
        decreases n - i,
    {
        let p = build_point(xs[i], ys[i]);
        assert(p.len() == 2);
        assert(p[0] == xs[i as int]);
        assert(p[1] == ys[i as int]);
        assert(0 <= p[0] <= 1000000000);
        assert(0 <= p[1] <= 1000000000);
        points.push(p);
        i = i + 1;
    }

    // Apply mutation to w
    let w_out: i32 = if mutation_kind == 0 {
        w                                          // identity
    } else if mutation_kind == 1 {
        0                                          // zero
    } else if mutation_kind == 2 {
        1_000_000_000                              // max boundary
    } else if mutation_kind == 3 {
        w / 2                                      // halve
    } else if mutation_kind == 4 && w < 1_000_000_000 {
        (w + 1) as i32                             // nudge up
    } else if mutation_kind == 5 && w > 0 {
        (w - 1) as i32                             // nudge down
    } else if mutation_kind == 6 {
        1                                          // small w
    } else {
        w                                          // fallback
    };

    (points, w_out)
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

fn random_coords(rng: &mut Rng, n: usize, max_val: i64) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_range_i64(0, max_val) as i32);
    }
    v
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(3111);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut n_emitted = 0usize;

    let mut emit = |points: Vec<Vec<i32>>, w: i32,
                    seen: &mut HashSet<String>,
                    out: &mut std::io::BufWriter<std::fs::File>,
                    n_emitted: &mut usize| {
        let mut points = points.clone();
        points.sort();
        let (points, w) = generate_test_case(points, w);
        if *n_emitted >= count {
            return;
        }
        let key = format!("{:?}|{}", points, w);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::min_rectangles_to_cover_points(points.clone(), w);
        writeln!(out, "{}", json!({
            "input": {"points": points, "w": w},
            "output": output
        })).unwrap();
        *n_emitted += 1;
    };

    // Example inputs from description.md
    let examples: Vec<(Vec<Vec<i32>>, i32)> = vec![
        (vec![vec![2,1],vec![1,0],vec![1,4],vec![1,8],vec![3,5],vec![4,6]], 1),
        (vec![vec![0,0],vec![1,1],vec![2,2],vec![3,3],vec![4,4],vec![5,5],vec![6,6]], 2),
        (vec![vec![2,3],vec![1,2]], 0),
    ];
    for (pts, w) in examples {
        emit(pts, w, &mut seen, &mut out, &mut n_emitted);
    }

    // Mutation kinds
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7];

    // Seed inputs: various interesting configurations
    let seed_configs: Vec<(Vec<i32>, Vec<i32>, i32)> = vec![
        // single point
        (vec![0], vec![0], 0),
        (vec![1000000000], vec![1000000000], 1000000000),
        // two points same x
        (vec![5, 5], vec![0, 10], 0),
        // two points different x
        (vec![0, 1000000000], vec![0, 1000000000], 500000000),
        // collinear x
        (vec![1, 2, 3, 4, 5], vec![0, 0, 0, 0, 0], 1),
        // spread out
        (vec![0, 100, 200, 300, 400], vec![50, 50, 50, 50, 50], 99),
        // all same point
        (vec![42, 42, 42], vec![7, 7, 7], 0),
        // boundary w
        (vec![0, 1], vec![0, 1], 1000000000),
    ];

    for (xs, ys, w) in &seed_configs {
        for &mk in &mutation_kinds {
            if n_emitted >= count { break; }
            let (points, w_out) = generate_candidate(xs, ys, *w, mk);
            emit(points, w_out, &mut seen, &mut out, &mut n_emitted);
        }
    }

    // Random test cases with diverse size classes and value ranges
    while n_emitted < count {
        // Size classes
        let n: usize = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 3),          // tiny
            1 => rng.gen_range_usize(1, 10),         // small
            2 => rng.gen_range_usize(11, 100),       // medium
            3 => rng.gen_range_usize(101, 1000),     // large
            _ => rng.gen_range_usize(1001, 5000),    // big
        };

        // Value range classes
        let max_coord: i64 = match rng.gen_range_usize(0, 3) {
            0 => 10,                                 // tiny values
            1 => 1000,                               // small values
            2 => 1_000_000,                          // medium values
            _ => 1_000_000_000,                      // full range
        };

        let xs = random_coords(&mut rng, n, max_coord);
        let ys = random_coords(&mut rng, n, max_coord);

        // w sampling with boundary values mixed in
        let w: i32 = if rng.gen_range_usize(0, 4) == 0 {
            // boundary values ~25% of the time
            *[0i32, 1, 1_000_000_000].get(rng.gen_range_usize(0, 2)).unwrap()
        } else {
            rng.gen_range_i64(0, max_coord) as i32
        };

        let mk = rng.gen_range_usize(0, 7) as u8;
        let (points, w_out) = generate_candidate(&xs, &ys, w, mk);
        emit(points, w_out, &mut seen, &mut out, &mut n_emitted);
    }
}
