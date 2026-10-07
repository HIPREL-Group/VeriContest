use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    col0: &Vec<i32>,
    col1: &Vec<i32>,
    col2: &Vec<i32>,
    t0: i32,
    t1: i32,
    t2: i32,
    mutation_kind: u8,
) -> (result: (Vec<Vec<i32>>, Vec<i32>))
    requires
        col0.len() == col1.len(),
        col1.len() == col2.len(),
        1 <= col0.len() <= 100_000,
        forall|i: int| 0 <= i < col0.len() ==> 1 <= #[trigger] col0[i] <= 1000,
        forall|i: int| 0 <= i < col1.len() ==> 1 <= #[trigger] col1[i] <= 1000,
        forall|i: int| 0 <= i < col2.len() ==> 1 <= #[trigger] col2[i] <= 1000,
        1 <= t0 <= 1000,
        1 <= t1 <= 1000,
        1 <= t2 <= 1000,
    ensures
        1 <= result.0.len() <= 100_000,
        result.1.len() == 3,
        forall |i: int| 0 <= i < result.0.len() ==> #[trigger] result.0[i].len() == 3,
        forall |i: int, j: int| 0 <= i < result.0.len() && 0 <= j < result.0[i].len() ==> 1 <= #[trigger] result.0[i][j] <= 1000,
        forall |j: int| 0 <= j < 3 ==> 1 <= #[trigger] result.1[j] <= 1000,
{
    let n = col0.len();

    // Build target with mutations on scalar components
    let mt0: i32 = if mutation_kind == 1 {
        1i32
    } else if mutation_kind == 2 {
        1000i32
    } else if mutation_kind == 3 && t0 < 1000 {
        (t0 + 1) as i32
    } else if mutation_kind == 4 && t0 > 1 {
        (t0 - 1) as i32
    } else {
        t0
    };
    let mt1: i32 = if mutation_kind == 5 {
        1i32
    } else if mutation_kind == 6 {
        1000i32
    } else {
        t1
    };
    let mt2: i32 = if mutation_kind == 7 {
        1i32
    } else if mutation_kind == 8 {
        1000i32
    } else {
        t2
    };

    let mut target: Vec<i32> = Vec::new();
    target.push(mt0);
    target.push(mt1);
    target.push(mt2);

    // Build triplets from column vectors
    let mut triplets: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;

    while i < n
        invariant
            0 <= i <= n,
            n == col0.len(),
            1 <= n <= 100_000,
            col0.len() == col1.len(),
            col1.len() == col2.len(),
            forall|k: int| 0 <= k < col0.len() ==> 1 <= #[trigger] col0[k] <= 1000,
            forall|k: int| 0 <= k < col1.len() ==> 1 <= #[trigger] col1[k] <= 1000,
            forall|k: int| 0 <= k < col2.len() ==> 1 <= #[trigger] col2[k] <= 1000,
            triplets.len() == i,
            forall|k: int| 0 <= k < i as int ==> #[trigger] triplets[k].len() == 3,
            forall|k: int, j: int| 0 <= k < i as int && 0 <= j < triplets[k].len()
                ==> 1 <= #[trigger] triplets[k][j] <= 1000,
        decreases n - i,
    {
        let mut row: Vec<i32> = Vec::new();
        row.push(col0[i]);
        row.push(col1[i]);
        row.push(col2[i]);

        assert(row.len() == 3);
        assert(1 <= row[0int] <= 1000);
        assert(1 <= row[1int] <= 1000);
        assert(1 <= row[2int] <= 1000);

        triplets.push(row);

        proof {
            assert(triplets[i as int].len() == 3);
            assert forall|k: int| 0 <= k < (i + 1) as int
                implies #[trigger] triplets[k].len() == 3 by {
                if k < i as int {
                } else {
                }
            };
            assert forall|k: int, j: int|
                0 <= k < (i + 1) as int && 0 <= j < triplets[k].len()
                implies 1 <= #[trigger] triplets[k][j] <= 1000 by {
                if k < i as int {
                } else {
                    assert(k == i as int);
                }
            };
        }

        i = i + 1;
    }

    (triplets, target)
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
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let mut count: usize = 0;

    use std::io::Write;
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);

    macro_rules! emit {
        ($c0:expr, $c1:expr, $c2:expr, $t0:expr, $t1:expr, $t2:expr, $mk:expr) => {{
            let (triplets, target) = generate_test_case(&$c0, &$c1, &$c2, $t0, $t1, $t2, $mk);
            let trip_vecs: Vec<Vec<i32>> = triplets;
            let tgt: Vec<i32> = target;
            let output = Solution::merge_triplets(
                trip_vecs.clone(),
                tgt.clone(),
            );
            let trip_json: Vec<serde_json::Value> = trip_vecs.iter()
                .map(|r| json!([r[0], r[1], r[2]]))
                .collect();
            writeln!(out, "{}", json!({
                "input": {"triplets": trip_json, "target": [tgt[0], tgt[1], tgt[2]]},
                "output": output
            })).unwrap();
            count += 1;
        }};
    }

    fn random_col(rng: &mut Rng, n: usize) -> Vec<i32> {
        (0..n).map(|_| rng.gen_range_i64(1, 1000) as i32).collect()
    }

    // ---- Example inputs from description.md ----
    // Example 1: triplets = [[2,5,3],[1,8,4],[1,7,5]], target = [2,7,5] -> true
    emit!(vec![2,1,1], vec![5,8,7], vec![3,4,5], 2, 7, 5, 0u8);
    // Example 2: triplets = [[3,4,5],[4,5,6]], target = [3,2,5] -> false
    emit!(vec![3,4], vec![4,5], vec![5,6], 3, 2, 5, 0u8);
    // Example 3: triplets = [[2,5,3],[2,3,4],[1,2,5],[5,2,3]], target = [5,5,5] -> true
    emit!(vec![2,2,1,5], vec![5,3,2,2], vec![3,4,5,3], 5, 5, 5, 0u8);

    // ---- Examples with all mutation kinds ----
    for mk in 0u8..=8 {
        emit!(vec![2,1,1], vec![5,8,7], vec![3,4,5], 2, 7, 5, mk);
    }

    // ---- Boundary target values with varied mutations ----
    for mk in 0u8..=8 {
        emit!(vec![1, 1000], vec![1, 1000], vec![1, 1000], 1, 1, 1, mk);
    }
    for mk in 0u8..=8 {
        emit!(vec![1000, 1], vec![1000, 1], vec![1000, 1], 1000, 1000, 1000, mk);
    }

    // ---- Single triplet ----
    emit!(vec![500], vec![500], vec![500], 500, 500, 500, 0u8);
    emit!(vec![1], vec![1], vec![1], 1, 1, 1, 0u8);
    emit!(vec![1000], vec![1000], vec![1000], 1000, 1000, 1000, 0u8);

    // ---- Random tiny arrays (1-5 triplets), all mutations ----
    for _ in 0..4 {
        let n = rng.gen_range_usize(1, 5);
        let c0 = random_col(&mut rng, n);
        let c1 = random_col(&mut rng, n);
        let c2 = random_col(&mut rng, n);
        let t0 = rng.gen_range_i64(1, 1000) as i32;
        let t1 = rng.gen_range_i64(1, 1000) as i32;
        let t2 = rng.gen_range_i64(1, 1000) as i32;
        for mk in 0u8..=8 {
            emit!(c0.clone(), c1.clone(), c2.clone(), t0, t1, t2, mk);
        }
    }

    // ---- Random small arrays (6-50 triplets), random mutations ----
    for _ in 0..6 {
        let n = rng.gen_range_usize(6, 50);
        let c0 = random_col(&mut rng, n);
        let c1 = random_col(&mut rng, n);
        let c2 = random_col(&mut rng, n);
        let t0 = rng.gen_range_i64(1, 1000) as i32;
        let t1 = rng.gen_range_i64(1, 1000) as i32;
        let t2 = rng.gen_range_i64(1, 1000) as i32;
        let mk = (rng.gen_range_usize(0, 8)) as u8;
        emit!(c0, c1, c2, t0, t1, t2, mk);
    }

    // ---- Random medium arrays (51-1000 triplets) ----
    for _ in 0..6 {
        let n = rng.gen_range_usize(51, 1000);
        let c0 = random_col(&mut rng, n);
        let c1 = random_col(&mut rng, n);
        let c2 = random_col(&mut rng, n);
        let t0 = rng.gen_range_i64(1, 1000) as i32;
        let t1 = rng.gen_range_i64(1, 1000) as i32;
        let t2 = rng.gen_range_i64(1, 1000) as i32;
        let mk = (rng.gen_range_usize(0, 8)) as u8;
        emit!(c0, c1, c2, t0, t1, t2, mk);
    }

    // ---- Random large arrays (1001-10000 triplets) ----
    for _ in 0..3 {
        let n = rng.gen_range_usize(1001, 10000);
        let c0 = random_col(&mut rng, n);
        let c1 = random_col(&mut rng, n);
        let c2 = random_col(&mut rng, n);
        let t0 = rng.gen_range_i64(1, 1000) as i32;
        let t1 = rng.gen_range_i64(1, 1000) as i32;
        let t2 = rng.gen_range_i64(1, 1000) as i32;
        let mk = (rng.gen_range_usize(0, 8)) as u8;
        emit!(c0, c1, c2, t0, t1, t2, mk);
    }

    // ---- Maximum size (100000 triplets) ----
    {
        let n = 100_000;
        let c0 = random_col(&mut rng, n);
        let c1 = random_col(&mut rng, n);
        let c2 = random_col(&mut rng, n);
        emit!(c0, c1, c2, 500, 500, 500, 0u8);
    }

    // ---- Fill remaining with random sizes and random mutations ----
    while count < goal {
        let n = match count % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 1000),
            _ => rng.gen_range_usize(1001, 10000),
        };
        let c0 = random_col(&mut rng, n);
        let c1 = random_col(&mut rng, n);
        let c2 = random_col(&mut rng, n);
        let t0 = if count % 5 == 0 { 1i32 }
            else if count % 7 == 0 { 1000i32 }
            else { rng.gen_range_i64(1, 1000) as i32 };
        let t1 = if count % 11 == 0 { 1i32 }
            else if count % 13 == 0 { 1000i32 }
            else { rng.gen_range_i64(1, 1000) as i32 };
        let t2 = if count % 17 == 0 { 1i32 }
            else if count % 19 == 0 { 1000i32 }
            else { rng.gen_range_i64(1, 1000) as i32 };
        let mk = (rng.gen_range_usize(0, 8)) as u8;
        emit!(c0, c1, c2, t0, t1, t2, mk);
    }

    eprintln!("Generated {} test cases to {:?}", count, out_path);
}
