use vstd::prelude::*;

verus! {

pub fn generate_test_case(hours: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= hours.len() <= 100,
        forall|i: int| 0 <= i < hours.len() ==> 1 <= #[trigger] hours[i] <= 1_000_000_000,
    ensures
        1 <= result.len() <= 100,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 1_000_000_000,
{
    if mutation_kind == 0 {
        // identity
        hours
    } else if mutation_kind == 1 {
        // set first element to 12 (half a day)
        let mut h = hours;
        h.set(0, 12);
        h
    } else if mutation_kind == 2 && hours.len() >= 2 {
        // set first two elements to 12 each (forms a complete day pair)
        let mut h = hours;
        h.set(0, 12);
        h.set(1, 12);
        h
    } else if mutation_kind == 3 {
        // set first element to 24 (a full day)
        let mut h = hours;
        h.set(0, 24);
        h
    } else if mutation_kind == 4 && hours.len() >= 2 {
        // set first two elements to 24 each (pair sums to 48)
        let mut h = hours;
        h.set(0, 24);
        h.set(1, 24);
        h
    } else if mutation_kind == 5 {
        // set all elements to 24
        let mut h = hours;
        let mut i: usize = 0;
        while i < h.len()
            invariant
                0 <= i <= h.len(),
                h.len() == hours.len(),
                1 <= h.len() <= 100,
                forall|j: int| 0 <= j < i ==> h[j] == 24,
                forall|j: int| i <= j < h.len() ==> h[j] == hours[j],
            decreases h.len() - i,
        {
            h.set(i, 24);
            i += 1;
        }
        h
    } else if mutation_kind == 6 {
        // set first element to 1 (boundary min)
        let mut h = hours;
        h.set(0, 1);
        h
    } else if mutation_kind == 7 {
        // set first element to 1_000_000_000 (boundary max)
        let mut h = hours;
        h.set(0, 1_000_000_000);
        h
    } else if mutation_kind == 8 && hours.len() < 100 {
        // grow array by one element (push 1)
        let mut h = hours;
        h.push(1);
        h
    } else if mutation_kind == 9 && hours.len() > 1 {
        // shrink array by one element
        let mut h = hours;
        h.pop();
        h
    } else if mutation_kind == 10 && hours.len() >= 2 {
        // set first two to complementary pair: 1 and 23 (1+23=24)
        let mut h = hours;
        h.set(0, 1);
        h.set(1, 23);
        h
    } else if mutation_kind == 11 {
        // set first element to 48 (two full days)
        let mut h = hours;
        h.set(0, 48);
        h
    } else {
        hours // fallback
    }
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
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

struct Solution;
include!("../code.rs");

fn mutate(hours: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(hours, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_hours(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut hours = Vec::with_capacity(len);
    for _ in 0..len {
        hours.push(rng.gen_range_i64(1, 1_000_000_000) as i32);
    }
    hours
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(3184);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |hours: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target {
            return;
        }
        let key = format!("{:?}", hours);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::count_complete_day_pairs(hours.clone());
        writeln!(out, "{}", json!({"input": {"hours": hours}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    emit(vec![12, 12, 30, 24, 24], &mut seen, &mut out, &mut count);
    emit(vec![72, 48, 24, 3], &mut seen, &mut out, &mut count);

    // Curated seed arrays
    let seeds: Vec<Vec<i32>> = vec![
        vec![1],
        vec![24],
        vec![12, 12],
        vec![24, 24],
        vec![1, 23],
        vec![6, 18, 12, 36],
        vec![1, 2, 3, 4, 5],
        vec![48, 48, 48],
        vec![1_000_000_000],
        vec![1, 1_000_000_000],
        vec![24, 48, 72, 96, 120],
        vec![7, 17, 5, 19, 11, 13],
        vec![1, 1, 1, 1, 1],
        vec![12, 36, 60, 84],
    ];

    let mutation_kinds: Vec<u8> = (0..=12).collect();

    // Apply every mutation to every seed
    for s in &seeds {
        for &mk in &mutation_kinds {
            let result = mutate(s.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Size classes with random mutations
    for i in 0..60 {
        let n: usize = match i % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 30),
            3 => rng.gen_range_usize(31, 70),
            _ => rng.gen_range_usize(71, 100),
        };
        let hours = random_hours(&mut rng, n);
        let mk = rng.gen_range_usize(0, 12) as u8;
        let result = mutate(hours, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }

    // Fill remaining with random identity
    while count < target {
        let n = rng.gen_range_usize(1, 100);
        let hours = random_hours(&mut rng, n);
        emit(mutate(hours, 0), &mut seen, &mut out, &mut count);
    }
}
