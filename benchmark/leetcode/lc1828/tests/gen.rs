use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    point_xs: Vec<i32>,
    point_ys: Vec<i32>,
    query_xs: Vec<i32>,
    query_ys: Vec<i32>,
    query_rs: Vec<i32>,
    mutation_kind: u8,
) -> (result: (Vec<Vec<i32>>, Vec<Vec<i32>>))
    requires
        1 <= point_xs.len() <= 500,
        point_ys.len() == point_xs.len(),
        forall|i: int| 0 <= i < point_xs.len() ==> 0 <= #[trigger] point_xs[i] <= 500,
        forall|i: int| 0 <= i < point_ys.len() ==> 0 <= #[trigger] point_ys[i] <= 500,
        1 <= query_xs.len() <= 500,
        query_ys.len() == query_xs.len(),
        query_rs.len() == query_xs.len(),
        forall|j: int| 0 <= j < query_xs.len() ==> 0 <= #[trigger] query_xs[j] <= 500,
        forall|j: int| 0 <= j < query_ys.len() ==> 0 <= #[trigger] query_ys[j] <= 500,
        forall|j: int| 0 <= j < query_rs.len() ==> 1 <= #[trigger] query_rs[j] <= 500,
    ensures
        1 <= result.0.len() <= 500,
        forall|i: int| 0 <= i < result.0.len() ==> #[trigger] result.0[i].len() == 2,
        forall|i: int|
            0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i][0] <= 500 && 0 <= result.0[i][1] <= 500,
        1 <= result.1.len() <= 500,
        forall|j: int| 0 <= j < result.1.len() ==> #[trigger] result.1[j].len() == 3,
        forall|j: int|
            0 <= j < result.1.len() ==> 0 <= #[trigger] result.1[j][0] <= 500 && 0 <= result.1[j][1] <= 500
                && 1 <= result.1[j][2] <= 500,
{
    // Apply mutations to flat arrays before construction
    let mut pxs = point_xs;
    let mut pys = point_ys;
    let mut qxs = query_xs;
    let mut qys = query_ys;
    let mut qrs = query_rs;

    if mutation_kind == 1 {
        // set first point to origin (0, 0)
        pxs.set(0, 0);
        pys.set(0, 0);
    } else if mutation_kind == 2 {
        // set first point to max corner (500, 500)
        pxs.set(0, 500);
        pys.set(0, 500);
    } else if mutation_kind == 3 {
        // set first query radius to minimum (1)
        qrs.set(0, 1);
    } else if mutation_kind == 4 {
        // set first query radius to maximum (500)
        qrs.set(0, 500);
    } else if mutation_kind == 5 {
        // center first query on first point
        qxs.set(0, pxs[0]);
        qys.set(0, pys[0]);
    } else if mutation_kind == 6 {
        // nudge first point x up by 1 if possible
        if pxs[0] < 500 {
            pxs.set(0, pxs[0] + 1);
        }
    } else if mutation_kind == 7 {
        // nudge first point y down by 1 if possible
        if pys[0] > 0 {
            pys.set(0, pys[0] - 1);
        }
    } else if mutation_kind == 8 {
        // set first query center to origin
        qxs.set(0, 0);
        qys.set(0, 0);
    } else if mutation_kind == 9 {
        // set first query center to (250, 250) center of domain
        qxs.set(0, 250);
        qys.set(0, 250);
    }
    // mutation_kind == 0 or other: identity

    // Build points: Vec<Vec<i32>> from flat arrays
    let mut points: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;
    while i < pxs.len()
        invariant
            0 <= i <= pxs.len(),
            points.len() == i as int,
            1 <= pxs.len() <= 500,
            pys.len() == pxs.len(),
            forall|k: int| 0 <= k < pxs.len() ==> 0 <= #[trigger] pxs[k] <= 500,
            forall|k: int| 0 <= k < pys.len() ==> 0 <= #[trigger] pys[k] <= 500,
            forall|k: int| 0 <= k < i ==> #[trigger] points[k].len() == 2,
            forall|k: int|
                0 <= k < i ==> 0 <= #[trigger] points[k][0] <= 500 && 0 <= points[k][1] <= 500,
        decreases pxs.len() - i,
    {
        let mut pt: Vec<i32> = Vec::new();
        pt.push(pxs[i]);
        pt.push(pys[i]);
        assert(pt.len() == 2);
        assert(pt[0] == pxs[i as int]);
        assert(pt[1] == pys[i as int]);
        points.push(pt);
        i += 1;
    }

    // Build queries: Vec<Vec<i32>> from flat arrays
    let mut queries: Vec<Vec<i32>> = Vec::new();
    let mut j: usize = 0;
    while j < qxs.len()
        invariant
            0 <= j <= qxs.len(),
            queries.len() == j as int,
            1 <= qxs.len() <= 500,
            qys.len() == qxs.len(),
            qrs.len() == qxs.len(),
            forall|k: int| 0 <= k < qxs.len() ==> 0 <= #[trigger] qxs[k] <= 500,
            forall|k: int| 0 <= k < qys.len() ==> 0 <= #[trigger] qys[k] <= 500,
            forall|k: int| 0 <= k < qrs.len() ==> 1 <= #[trigger] qrs[k] <= 500,
            forall|k: int| 0 <= k < j ==> #[trigger] queries[k].len() == 3,
            forall|k: int|
                0 <= k < j ==> 0 <= #[trigger] queries[k][0] <= 500
                    && 0 <= queries[k][1] <= 500 && 1 <= queries[k][2] <= 500,
        decreases qxs.len() - j,
    {
        let mut q: Vec<i32> = Vec::new();
        q.push(qxs[j]);
        q.push(qys[j]);
        q.push(qrs[j]);
        assert(q.len() == 3);
        assert(q[0] == qxs[j as int]);
        assert(q[1] == qys[j as int]);
        assert(q[2] == qrs[j as int]);
        queries.push(q);
        j += 1;
    }

    (points, queries)
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

fn random_coord_arrays(rng: &mut Rng, len: usize) -> (Vec<i32>, Vec<i32>) {
    let mut xs = Vec::with_capacity(len);
    let mut ys = Vec::with_capacity(len);
    for _ in 0..len {
        xs.push(rng.gen_range_i64(0, 500) as i32);
        ys.push(rng.gen_range_i64(0, 500) as i32);
    }
    (xs, ys)
}

fn random_query_arrays(rng: &mut Rng, len: usize) -> (Vec<i32>, Vec<i32>, Vec<i32>) {
    let mut xs = Vec::with_capacity(len);
    let mut ys = Vec::with_capacity(len);
    let mut rs = Vec::with_capacity(len);
    for _ in 0..len {
        xs.push(rng.gen_range_i64(0, 500) as i32);
        ys.push(rng.gen_range_i64(0, 500) as i32);
        rs.push(rng.gen_range_i64(1, 500) as i32);
    }
    (xs, ys, rs)
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1828);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    let mut emit = |points: Vec<Vec<i32>>,
                    queries: Vec<Vec<i32>>,
                    seen: &mut HashSet<String>,
                    out: &mut std::io::BufWriter<std::fs::File>,
                    count: &mut usize| {
        if *count >= target_count {
            return;
        }
        let key = format!("{:?}{:?}", points, queries);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::count_points(points.clone(), queries.clone());
        writeln!(
            out,
            "{}",
            json!({"input": {"points": points, "queries": queries}, "output": output})
        )
        .unwrap();
        *count += 1;
    };

    // Example inputs from the problem description
    let example_points: Vec<Vec<Vec<i32>>> = vec![
        vec![vec![1, 3], vec![3, 3], vec![5, 3], vec![2, 2]],
        vec![vec![1, 1], vec![2, 2], vec![3, 3], vec![4, 4], vec![5, 5]],
    ];
    let example_queries: Vec<Vec<Vec<i32>>> = vec![
        vec![vec![2, 3, 1], vec![4, 3, 1], vec![1, 1, 2]],
        vec![vec![1, 2, 2], vec![2, 2, 2], vec![4, 3, 2], vec![4, 3, 3]],
    ];
    for idx in 0..example_points.len() {
        emit(
            example_points[idx].clone(),
            example_queries[idx].clone(),
            &mut seen,
            &mut out,
            &mut count,
        );
    }

    // Seed pools with diverse size classes
    let point_sizes: Vec<usize> = vec![1, 2, 3, 5, 10, 50, 100, 250, 500];
    let query_sizes: Vec<usize> = vec![1, 2, 3, 5, 10, 50, 100, 250, 500];

    // Apply each mutation to seeds of varied sizes
    for &np in &point_sizes {
        for &nq in &query_sizes {
            if count >= target_count {
                break;
            }
            let (pxs, pys) = random_coord_arrays(&mut rng, np);
            let (qxs, qys, qrs) = random_query_arrays(&mut rng, nq);
            for &mk in &mutation_kinds {
                if count >= target_count {
                    break;
                }
                let (points, queries) =
                    generate_test_case(pxs.clone(), pys.clone(), qxs.clone(), qys.clone(), qrs.clone(), mk);
                emit(points, queries, &mut seen, &mut out, &mut count);
            }
        }
    }

    // Boundary test cases
    // Single point, single query with radius 1
    {
        let (points, queries) =
            generate_test_case(vec![0], vec![0], vec![0], vec![0], vec![1], 0);
        emit(points, queries, &mut seen, &mut out, &mut count);
    }
    // Single point at max, single query at max
    {
        let (points, queries) =
            generate_test_case(vec![500], vec![500], vec![500], vec![500], vec![500], 0);
        emit(points, queries, &mut seen, &mut out, &mut count);
    }

    // Fill remaining with random inputs + random mutations
    while count < target_count {
        let np = match count % 5 {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 300),
            _ => rng.gen_range_usize(301, 500),
        };
        let nq = match count % 5 {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 300),
            _ => rng.gen_range_usize(301, 500),
        };
        let (pxs, pys) = random_coord_arrays(&mut rng, np);
        let (qxs, qys, qrs) = random_query_arrays(&mut rng, nq);
        let mk = rng.gen_range_usize(0, 9) as u8;
        let (points, queries) = generate_test_case(pxs, pys, qxs, qys, qrs, mk);
        emit(points, queries, &mut seen, &mut out, &mut count);
    }
}
