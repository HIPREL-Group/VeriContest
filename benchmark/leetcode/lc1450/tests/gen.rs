use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    bases: Vec<i32>,
    deltas: Vec<i32>,
    query_time: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, Vec<i32>, i32))
    requires
        bases.len() == deltas.len(),
        1 <= bases.len() <= 100,
        forall|i: int| #![trigger bases[i]] 0 <= i < bases.len() ==>
            1 <= bases[i] <= 1000
            && 0 <= deltas[i]
            && bases[i] + deltas[i] <= 1000,
        1 <= query_time <= 1000,
    ensures
        result.0.len() == result.1.len(),
        1 <= result.0.len() <= 100,
        forall|i: int| 0 <= i < result.0.len() ==>
            1 <= #[trigger] result.0[i] <= result.1[i] <= 1000,
        1 <= result.2 <= 1000,
{
    let n = bases.len();
    let mut end_time: Vec<i32> = Vec::new();
    let mut k: usize = 0;
    while k < n
        invariant
            0 <= k <= n,
            n == bases.len(),
            n == deltas.len(),
            1 <= n <= 100,
            end_time.len() == k,
            forall|j: int| #![trigger bases[j]] 0 <= j < n as int ==>
                1 <= bases[j] <= 1000
                && 0 <= deltas[j]
                && bases[j] + deltas[j] <= 1000,
            forall|j: int| 0 <= j < k as int ==>
                1 <= bases[j] <= #[trigger] end_time[j] <= 1000,
        decreases n - k,
    {
        end_time.push(bases[k] + deltas[k]);
        k += 1;
    }

    let start_time = bases;
    proof {
        assert(start_time.len() == end_time.len());
        assert(1 <= start_time.len() <= 100);
        assert forall|j: int| 0 <= j < start_time.len() implies
            1 <= #[trigger] start_time[j] <= end_time[j] <= 1000 by {}
    }

    if mutation_kind == 0 {
        (start_time, end_time, query_time)
    } else if mutation_kind == 1 {
        let q = start_time[0];
        (start_time, end_time, q)
    } else if mutation_kind == 2 {
        let q = end_time[0];
        (start_time, end_time, q)
    } else if mutation_kind == 3 {
        (start_time, end_time, 1)
    } else if mutation_kind == 4 {
        (start_time, end_time, 1000)
    } else if mutation_kind == 5 && query_time < 1000 {
        (start_time, end_time, query_time + 1)
    } else if mutation_kind == 6 && query_time > 1 {
        (start_time, end_time, query_time - 1)
    } else if mutation_kind == 7 && start_time.len() >= 2 {
        let mut st = start_time;
        let mut et = end_time;
        let tmp_s = st[0];
        let tmp_e = et[0];
        st.set(0, st[1]);
        et.set(0, et[1]);
        st.set(1, tmp_s);
        et.set(1, tmp_e);
        (st, et, query_time)
    } else if mutation_kind == 8 {
        let last = start_time.len() - 1;
        let mut et = end_time;
        et.set(last, start_time[last]);
        (start_time, et, query_time)
    } else if mutation_kind == 9 {
        let last = end_time.len() - 1;
        let q = end_time[last];
        (start_time, end_time, q)
    } else {
        (start_time, end_time, query_time)
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

fn random_pair_arrays(rng: &mut Rng, len: usize) -> (Vec<i32>, Vec<i32>) {
    let mut bases = Vec::with_capacity(len);
    let mut deltas = Vec::with_capacity(len);
    for _ in 0..len {
        let s = rng.gen_range_i64(1, 1000) as i32;
        let d = rng.gen_range_i64(0, (1000 - s) as i64) as i32;
        bases.push(s);
        deltas.push(d);
    }
    (bases, deltas)
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let num_mutations: u8 = 10;

    let mut emit = |st: Vec<i32>, et: Vec<i32>, qt: i32,
                    seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>,
                    count: &mut usize| {
        if *count >= target {
            return;
        }
        let key = format!("{:?}_{:?}_{}", st, et, qt);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::busy_student(st.clone(), et.clone(), qt);
        writeln!(out, "{}", json!({
            "input": {"startTime": st, "endTime": et, "queryTime": qt},
            "output": output
        })).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let example_bases: Vec<(Vec<i32>, Vec<i32>, i32)> = vec![
        (vec![1, 2, 3], vec![2, 0, 4], 4),
        (vec![4], vec![0], 4),
    ];

    for (bases, deltas, qt) in &example_bases {
        for mk in 0..num_mutations {
            let (st, et, q) = generate_test_case(bases.clone(), deltas.clone(), *qt, mk);
            emit(st, et, q, &mut seen, &mut out, &mut count);
        }
    }

    // Hand-crafted seed cases
    let seeds: Vec<(Vec<i32>, Vec<i32>, i32)> = vec![
        (vec![1], vec![0], 1),
        (vec![1], vec![999], 500),
        (vec![500, 500, 500], vec![0, 0, 0], 500),
        (vec![1, 1, 1], vec![999, 999, 999], 500),
        (vec![100, 200, 300], vec![10, 10, 10], 500),
        (vec![1, 2, 3], vec![0, 0, 0], 1),
        (vec![998, 999, 1000], vec![2, 1, 0], 1000),
        (vec![1, 100], vec![50, 50], 30),
        (vec![1], vec![999], 1000),
        (vec![1000], vec![0], 1000),
    ];

    for (bases, deltas, qt) in &seeds {
        for mk in 0..num_mutations {
            let (st, et, q) = generate_test_case(bases.clone(), deltas.clone(), *qt, mk);
            emit(st, et, q, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds with mutations across size classes
    for i in 0..80 {
        let len = match i % 5 {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 30),
            3 => rng.gen_range_usize(31, 70),
            _ => rng.gen_range_usize(71, 100),
        };
        let (bases, deltas) = random_pair_arrays(&mut rng, len);
        let qt = rng.gen_range_i64(1, 1000) as i32;
        let mk = rng.gen_range_usize(0, 9) as u8;
        let (st, et, q) = generate_test_case(bases, deltas, qt, mk);
        emit(st, et, q, &mut seen, &mut out, &mut count);
    }

    while count < target {
        let len = rng.gen_range_usize(1, 100);
        let (bases, deltas) = random_pair_arrays(&mut rng, len);
        let qt = rng.gen_range_i64(1, 1000) as i32;
        let (st, et, q) = generate_test_case(bases, deltas, qt, 0);
        emit(st, et, q, &mut seen, &mut out, &mut count);
    }
}
