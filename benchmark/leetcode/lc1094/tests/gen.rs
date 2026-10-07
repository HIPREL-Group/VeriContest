use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    passengers: &Vec<i32>,
    froms: &Vec<i32>,
    gaps: &Vec<i32>,
    capacity: i32,
    mutation_kind: u8,
) -> (result: (Vec<Vec<i32>>, i32))
    requires
        passengers.len() == froms.len(),
        froms.len() == gaps.len(),
        1 <= passengers.len() <= 1000,
        1 <= capacity <= 100_000i32,
        forall|i: int| 0 <= i < passengers.len() ==> 1 <= #[trigger] passengers[i] <= 100,
        forall|i: int| 0 <= i < froms.len() ==> 0 <= #[trigger] froms[i] <= 999,
        forall|i: int| 0 <= i < gaps.len() ==> 1 <= #[trigger] gaps[i],
        forall|i: int| 0 <= i < froms.len() ==> froms[i] + #[trigger] gaps[i] <= 1000,
    ensures
        1 <= result.0.len() <= 1000,
        1 <= result.1 <= 100_000i32,
        forall |i: int| 0 <= i < result.0.len() ==> #[trigger] result.0[i]@.len() == 3,
        forall |i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i][0] <= 100,
        forall |i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i][1] < result.0[i][2] <= 1000,
{
    let n = passengers.len();
    let mut trips: Vec<Vec<i32>> = Vec::new();

    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == passengers.len(),
            n == froms.len(),
            n == gaps.len(),
            1 <= n <= 1000,
            trips.len() == i,
            forall|k: int| 0 <= k < passengers.len() ==> 1 <= #[trigger] passengers[k] <= 100,
            forall|k: int| 0 <= k < froms.len() ==> 0 <= #[trigger] froms[k] <= 999,
            forall|k: int| 0 <= k < gaps.len() ==> 1 <= #[trigger] gaps[k],
            forall|k: int| 0 <= k < froms.len() ==> froms[k] + #[trigger] gaps[k] <= 1000,
            forall|k: int| 0 <= k < i ==> #[trigger] trips[k]@.len() == 3,
            forall|k: int| 0 <= k < i ==> 1 <= #[trigger] trips[k][0] <= 100,
            forall|k: int| 0 <= k < i ==> 0 <= #[trigger] trips[k][1] < trips[k][2] <= 1000,
        decreases n - i,
    {
        let mut trip: Vec<i32> = Vec::new();
        trip.push(passengers[i]);
        trip.push(froms[i]);
        trip.push(froms[i] + gaps[i]);
        assert(trip@.len() == 3);
        assert(1 <= trip[0] <= 100);
        assert(0 <= trip[1] < trip[2] <= 1000);
        trips.push(trip);
        i += 1;
    }

    let cap = if mutation_kind == 0 {
        capacity
    } else if mutation_kind == 1 {
        1i32
    } else if mutation_kind == 2 {
        100_000i32
    } else if mutation_kind == 3 && capacity <= 50_000 {
        capacity * 2
    } else if mutation_kind == 4 && capacity >= 2 {
        capacity / 2
    } else {
        capacity
    };

    (trips, cap)
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

fn random_trip_components(rng: &mut Rng, n: usize) -> (Vec<i32>, Vec<i32>, Vec<i32>) {
    let mut passengers = Vec::with_capacity(n);
    let mut froms = Vec::with_capacity(n);
    let mut gaps = Vec::with_capacity(n);
    for _ in 0..n {
        passengers.push(rng.gen_range_i64(1, 100) as i32);
        let f = rng.gen_range_i64(0, 999) as i32;
        let max_gap = 1000 - f;
        let g = rng.gen_range_i64(1, max_gap as i64) as i32;
        froms.push(f);
        gaps.push(g);
    }
    (passengers, froms, gaps)
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1094);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut total = 0usize;

    let mut emit = |trips_vecs: Vec<Vec<i32>>, capacity: i32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, total: &mut usize| {
        if *total >= count {
            return;
        }
        let key = format!("{:?}_{}", trips_vecs, capacity);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::car_pooling(trips_vecs.clone(), capacity);
        writeln!(out, "{}", json!({
            "input": {"trips": trips_vecs, "capacity": capacity},
            "output": output
        })).unwrap();
        *total += 1;
    };

    // Example 1: trips = [[2,1,5],[3,3,7]], capacity = 4 -> false
    emit(vec![vec![2,1,5], vec![3,3,7]], 4, &mut seen, &mut out, &mut total);
    // Example 2: trips = [[2,1,5],[3,3,7]], capacity = 5 -> true
    emit(vec![vec![2,1,5], vec![3,3,7]], 5, &mut seen, &mut out, &mut total);

    // Edge cases
    // Single trip
    emit(vec![vec![1,0,1]], 1, &mut seen, &mut out, &mut total);
    // Single trip at max boundaries
    emit(vec![vec![100,0,1000]], 100, &mut seen, &mut out, &mut total);
    emit(vec![vec![100,0,1000]], 99, &mut seen, &mut out, &mut total);
    // Max capacity
    emit(vec![vec![1,0,1]], 100_000, &mut seen, &mut out, &mut total);
    // Min capacity with overload
    emit(vec![vec![2,0,1]], 1, &mut seen, &mut out, &mut total);

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4];

    // Generate via verified generator with diverse sizes and mutations
    for i in 0..80 {
        if total >= count { break; }
        let n = match i % 5 {
            0 => rng.gen_range_usize(1, 3),       // tiny
            1 => rng.gen_range_usize(1, 10),      // small
            2 => rng.gen_range_usize(11, 50),     // medium
            3 => rng.gen_range_usize(51, 200),    // large
            _ => rng.gen_range_usize(201, 1000),  // max
        };
        let capacity = match i % 4 {
            0 => 1i32,
            1 => rng.gen_range_i64(1, 100) as i32,
            2 => rng.gen_range_i64(1, 100_000) as i32,
            _ => 100_000i32,
        };
        let (passengers, froms, gaps) = random_trip_components(&mut rng, n);
        let mk = mutation_kinds[rng.gen_range_usize(0, mutation_kinds.len() - 1)];
        let (trips, cap) = generate_test_case(&passengers, &froms, &gaps, capacity, mk);
        emit(trips, cap, &mut seen, &mut out, &mut total);
    }

    // Fill remaining
    while total < count {
        let n = rng.gen_range_usize(1, 1000);
        let capacity = rng.gen_range_i64(1, 100_000) as i32;
        let (passengers, froms, gaps) = random_trip_components(&mut rng, n);
        let mk = rng.gen_range_usize(0, 4) as u8;
        let (trips, cap) = generate_test_case(&passengers, &froms, &gaps, capacity, mk);
        emit(trips, cap, &mut seen, &mut out, &mut total);
    }
}
