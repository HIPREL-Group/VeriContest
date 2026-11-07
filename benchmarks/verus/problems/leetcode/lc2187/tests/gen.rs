use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    raw_times: &Vec<i32>,
    total_trips: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= raw_times.len() <= 100000,
        forall|i: int| 0 <= i < raw_times.len() ==> 0 <= #[trigger] raw_times[i] <= 9999999,
        1 <= total_trips <= 10000000,
    ensures
        1 <= result.0.len() <= 100000,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 10000000,
        1 <= result.1 <= 10000000,
{
    // Build the time array by shifting each raw value by +1
    let mut time: Vec<i32> = Vec::new();
    let mut idx: usize = 0;
    while idx < raw_times.len()
        invariant
            0 <= idx <= raw_times.len(),
            time.len() == idx,
            1 <= raw_times.len() <= 100000,
            forall|i: int| 0 <= i < raw_times.len() ==> 0 <= #[trigger] raw_times[i] <= 9999999,
            forall|i: int| 0 <= i < time.len() ==> 1 <= #[trigger] time[i] <= 10000000,
        decreases raw_times.len() - idx,
    {
        let val = raw_times[idx] + 1;
        time.push(val);
        idx = idx + 1;
    }

    // Apply mutations
    let mutated_trips: i32 =
        if mutation_kind == 4 && total_trips > 1 {
            (total_trips - 1) as i32
        } else if mutation_kind == 5 && total_trips < 10000000 {
            (total_trips + 1) as i32
        } else if mutation_kind == 6 {
            1i32
        } else if mutation_kind == 7 {
            10000000i32
        } else {
            total_trips
        };

    if mutation_kind == 1 && time.len() > 0 {
        // Set first element to 1 (fastest bus)
        let last = time.len() - 1;
        time.set(last, 1i32);
    } else if mutation_kind == 2 && time.len() > 0 {
        // Set first element to max (slowest bus)
        let last = time.len() - 1;
        time.set(last, 10000000i32);
    } else if mutation_kind == 3 && time.len() > 0 {
        // Set all elements to the same value
        let fill_val = time[0];
        let mut j: usize = 0;
        while j < time.len()
            invariant
                0 <= j <= time.len(),
                1 <= time.len() <= 100000,
                1 <= fill_val <= 10000000,
                forall|i: int| 0 <= i < time.len() ==> 1 <= #[trigger] time[i] <= 10000000,
            decreases time.len() - j,
        {
            time.set(j, fill_val);
            j = j + 1;
        }
    } else if mutation_kind == 8 && time.len() >= 2 {
        // Swap first and last elements
        let last = time.len() - 1;
        let tmp = time[0];
        time.set(0, time[last]);
        time.set(last, tmp);
    } else if mutation_kind == 9 && time.len() > 0 {
        // Set first element to midpoint value
        time.set(0, 5000000i32);
    }

    (time, mutated_trips)
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

fn random_raw_times(rng: &mut Rng, n: usize, max_val: i32) -> Vec<i32> {
    let mut v = Vec::new();
    for _ in 0..n {
        v.push(rng.gen_range_i64(0, max_val as i64) as i32);
    }
    v
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    use std::io::Write;
    use std::collections::HashSet;
    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut emitted = 0usize;

    macro_rules! emit {
        ($raw:expr, $trips:expr, $mk:expr) => {
            if emitted < count {
                let raw_val: Vec<i32> = $raw;
                let trips_val: i32 = $trips;
                let mk_val: u8 = $mk;
                let (time_out, trips_out) = generate_test_case(
                    &raw_val, trips_val, mk_val,
                );
                let result = Solution::minimum_time(time_out.clone(), trips_out);
                let line = json!({
                    "input": {"time": time_out, "totalTrips": trips_out},
                    "output": result
                }).to_string();
                if seen.insert(line.clone()) {
                    writeln!(out, "{}", line).unwrap();
                    emitted += 1;
                }
            }
        };
    }

    // ---- LeetCode examples ----
    // Example 1: time = [1,2,3], totalTrips = 5 => 3
    emit!(vec![0, 1, 2], 5, 0);
    // Example 2: time = [2], totalTrips = 1 => 2
    emit!(vec![1], 1, 0);

    // ---- Boundary: single bus, all mutations ----
    for mk in 0u8..=9 {
        emit!(vec![0], 1, mk);          // fastest bus, 1 trip
        emit!(vec![9999999], 1, mk);    // slowest bus, 1 trip
        emit!(vec![0], 10000000, mk);   // fastest bus, max trips
    }

    // ---- Small arrays (2-5 elements), all mutations ----
    for mk in 0u8..=9 {
        emit!(vec![0, 0], 5, mk);                     // two fastest
        emit!(vec![0, 9999999], 3, mk);                // mixed
        emit!(vec![0, 1, 2, 3, 4], 10, mk);           // 5 elements
    }

    // ---- Uniform arrays, varied trips ----
    for trips in [1i32, 2, 10, 100, 1000, 10000000] {
        emit!(vec![0; 10], trips, 0);         // all time=1
        emit!(vec![9999999; 10], trips, 0);   // all time=10000000
    }

    // ---- Random tiny arrays (1-5), all mutations ----
    for _ in 0..3 {
        let n = rng.gen_range_usize(1, 5);
        let raw = random_raw_times(&mut rng, n, 9999999);
        let trips = rng.gen_range_i64(1, 10000000) as i32;
        for mk in 0u8..=9 {
            emit!(raw.clone(), trips, mk);
        }
    }

    // ---- Random small arrays (6-50) ----
    for _ in 0..5 {
        let n = rng.gen_range_usize(6, 50);
        let raw = random_raw_times(&mut rng, n, 9999999);
        let trips = rng.gen_range_i64(1, 10000000) as i32;
        let mk = (rng.next_u64() % 10) as u8;
        emit!(raw, trips, mk);
    }

    // ---- Random medium arrays (51-1000) ----
    for _ in 0..5 {
        let n = rng.gen_range_usize(51, 1000);
        let raw = random_raw_times(&mut rng, n, 9999999);
        let trips = rng.gen_range_i64(1, 10000000) as i32;
        let mk = (rng.next_u64() % 10) as u8;
        emit!(raw, trips, mk);
    }

    // ---- Random large arrays (1001-10000) ----
    for _ in 0..3 {
        let n = rng.gen_range_usize(1001, 10000);
        let raw = random_raw_times(&mut rng, n, 9999999);
        let trips = rng.gen_range_i64(1, 10000000) as i32;
        let mk = (rng.next_u64() % 10) as u8;
        emit!(raw, trips, mk);
    }

    // ---- Max size array ----
    {
        let raw = vec![0i32; 100000];
        emit!(raw.clone(), 1, 0);
        emit!(raw.clone(), 10000000, 0);
        let raw2 = vec![9999999i32; 100000];
        emit!(raw2, 1, 0);
    }

    // ---- Boundary trips with various arrays ----
    for _ in 0..3 {
        let n = rng.gen_range_usize(1, 100);
        let raw = random_raw_times(&mut rng, n, 9999999);
        emit!(raw.clone(), 1, 0);
        emit!(raw.clone(), 10000000, 0);
    }

    // ---- Fill remaining with random ----
    while emitted < count {
        let n = match emitted % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 1000),
            _ => rng.gen_range_usize(1001, 10000),
        };
        let raw = random_raw_times(&mut rng, n, 9999999);
        let trips = if emitted % 5 == 0 {
            *[1i32, 10000000, 1000, 100, 10].iter().nth(
                (rng.next_u64() as usize) % 5
            ).unwrap()
        } else {
            rng.gen_range_i64(1, 10000000) as i32
        };
        let mk = (rng.next_u64() % 10) as u8;
        emit!(raw, trips, mk);
    }
}
