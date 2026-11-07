use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_jobs: Vec<i32>, d: i32, mutation_kind: u8) -> (job_difficulty: Vec<i32>)
    requires
        1 <= seed_jobs.len() <= 300,
        forall|i: int| 0 <= i < seed_jobs.len() ==> 0 <= #[trigger] seed_jobs[i] <= 1000,
        1 <= d <= 10,
    ensures
        1 <= job_difficulty.len() <= 300,
        forall|i: int| 0 <= i < job_difficulty.len() ==> 0 <= #[trigger] job_difficulty[i] <= 1000,
        1 <= d <= 10,
{
    if mutation_kind == 0 {
        seed_jobs
    } else if mutation_kind == 1 {
        let mut jd = seed_jobs;
        let last = jd.len() - 1;
        jd.set(last, 0);
        jd
    } else if mutation_kind == 2 {
        let mut jd = seed_jobs;
        let last = jd.len() - 1;
        jd.set(last, 1000);
        jd
    } else if mutation_kind == 3 {
        let mut jd = seed_jobs;
        let mut i: usize = 0;
        while i < jd.len()
            invariant
                0 <= i <= jd.len(),
                jd.len() == seed_jobs.len(),
                1 <= jd.len() <= 300,
                forall|j: int| 0 <= j < i ==> jd[j] == 500,
                forall|j: int| i <= j < jd.len() ==> jd[j] == seed_jobs[j],
            decreases jd.len() - i,
        {
            jd.set(i, 500);
            i += 1;
        }
        jd
    } else if mutation_kind == 4 && seed_jobs.len() < 300 {
        let mut jd = seed_jobs;
        jd.push(0);
        jd
    } else if mutation_kind == 5 && seed_jobs.len() > 1 {
        let mut jd = seed_jobs;
        jd.pop();
        jd
    } else if mutation_kind == 6 {
        let mut jd = seed_jobs;
        if jd[0] < 1000 {
            jd.set(0, jd[0] + 1);
        }
        jd
    } else if mutation_kind == 7 {
        let mut jd = seed_jobs;
        if jd[0] > 0 {
            jd.set(0, jd[0] - 1);
        }
        jd
    } else if mutation_kind == 8 {
        let mut jd = seed_jobs;
        jd.set(0, 0);
        let last = jd.len() - 1;
        jd.set(last, 1000);
        jd
    } else {
        seed_jobs
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

fn mutate(seed_jobs: Vec<i32>, d: i32, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(seed_jobs, d, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_job_difficulty(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut jd = Vec::with_capacity(len);
    for _ in 0..len {
        jd.push(rng.gen_range_i64(0, 1000) as i32);
    }
    jd
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1335);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |jd: Vec<i32>, d: i32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count {
            return;
        }
        let key = format!("{:?}_{}", jd, d);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::min_difficulty(jd.clone(), d);
        writeln!(out, "{}", json!({
            "input": {"job_difficulty": jd, "d": d},
            "output": output
        })).unwrap();
        *count += 1;
    };

    let examples: Vec<(Vec<i32>, i32)> = vec![
        (vec![6, 5, 4, 3, 2, 1], 2),
        (vec![9, 9, 9], 4),
        (vec![1, 1, 1], 3),
    ];
    for (jd, d) in examples {
        emit(jd, d, &mut seen, &mut out, &mut count);
    }

    let seed_inputs: Vec<Vec<i32>> = vec![
        vec![0],
        vec![1000],
        vec![0, 0, 0],
        vec![1000, 1000, 1000],
        vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
        vec![10, 9, 8, 7, 6, 5, 4, 3, 2, 1],
        vec![500],
        vec![0, 1000],
        vec![1000, 0],
        vec![100, 200, 300, 400, 500],
    ];

    let d_values: Vec<i32> = vec![1, 2, 3, 5, 10];
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8];

    for seed_jd in &seed_inputs {
        for &d in &d_values {
            for &mk in &mutation_kinds {
                let result = mutate(seed_jd.clone(), d, mk);
                emit(result, d, &mut seen, &mut out, &mut count);
            }
        }
    }

    while count < target_count {
        let n: usize = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 50),
            3 => rng.gen_range_usize(51, 150),
            _ => rng.gen_range_usize(151, 300),
        };
        let jd = random_job_difficulty(&mut rng, n);
        let d = rng.gen_range_i64(1, 10) as i32;
        let mk = rng.gen_range_usize(0, 8) as u8;
        let result = mutate(jd, d, mk);
        emit(result, d, &mut seen, &mut out, &mut count);
    }
}
