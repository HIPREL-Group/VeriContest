use vstd::prelude::*;

verus! {

pub fn generate_test_case(temperatures: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= temperatures.len() <= 100_000,
        forall|i: int| 0 <= i < temperatures.len() ==> 30 <= #[trigger] temperatures[i] <= 100,
    ensures
        1 <= result.len() <= 100_000,
        forall|i: int| 0 <= i < result.len() ==> 30 <= #[trigger] result[i] <= 100,
{
    if mutation_kind == 0 {
        // identity
        temperatures
    } else if mutation_kind == 1 {
        // set last element to 30 (min boundary)
        let mut t = temperatures;
        let last = t.len() - 1;
        t.set(last, 30);
        t
    } else if mutation_kind == 2 {
        // set last element to 100 (max boundary)
        let mut t = temperatures;
        let last = t.len() - 1;
        t.set(last, 100);
        t
    } else if mutation_kind == 3 {
        // set all elements to 50 (constant array)
        let mut t = temperatures;
        let mut i: usize = 0;
        while i < t.len()
            invariant
                0 <= i <= t.len(),
                t.len() == temperatures.len(),
                1 <= t.len() <= 100_000,
                forall|j: int| 0 <= j < i ==> t[j] == 50,
                forall|j: int| i <= j < t.len() ==> t[j] == temperatures[j],
            decreases t.len() - i,
        {
            t.set(i, 50);
            i += 1;
        }
        t
    } else if mutation_kind == 4 && temperatures.len() < 100_000 {
        // grow by one element (push 65)
        let mut t = temperatures;
        t.push(65);
        t
    } else if mutation_kind == 5 && temperatures.len() > 1 {
        // shrink by one element (pop)
        let mut t = temperatures;
        t.pop();
        t
    } else if mutation_kind == 6 {
        // nudge last element up: if < 100, increment by 1
        let mut t = temperatures;
        let last = t.len() - 1;
        if t[last] < 100 {
            t.set(last, t[last] + 1);
        }
        t
    } else if mutation_kind == 7 {
        // nudge last element down: if > 30, decrement by 1
        let mut t = temperatures;
        let last = t.len() - 1;
        if t[last] > 30 {
            t.set(last, t[last] - 1);
        }
        t
    } else if mutation_kind == 8 {
        // set first element to 30
        let mut t = temperatures;
        t.set(0, 30);
        t
    } else if mutation_kind == 9 {
        // set first element to 100
        let mut t = temperatures;
        t.set(0, 100);
        t
    } else if mutation_kind == 10 && temperatures.len() >= 2 {
        // swap first and last elements
        let mut t = temperatures;
        let last = t.len() - 1;
        let first_val = t[0];
        let last_val = t[last];
        t.set(0, last_val);
        t.set(last, first_val);
        t
    } else {
        // fallback
        temperatures
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

fn mutate(temperatures: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(temperatures, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_temps(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut temps = Vec::with_capacity(len);
    for _ in 0..len {
        temps.push(rng.gen_range_i64(30, 100) as i32);
    }
    temps
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(739);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |temps: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target {
            return;
        }
        let key = format!("{:?}", temps);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::daily_temperatures(temps.clone());
        writeln!(out, "{}", json!({"input": {"temperatures": temps}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![73, 74, 75, 71, 69, 72, 76, 73],
        vec![30, 40, 50, 60],
        vec![30, 60, 90],
    ];
    for ex in &examples {
        emit(ex.clone(), &mut seen, &mut out, &mut count);
    }

    // Hand-crafted seed arrays
    let seeds: Vec<Vec<i32>> = vec![
        vec![30],                          // single element, min temp
        vec![100],                         // single element, max temp
        vec![65],                          // single element, mid temp
        vec![30, 100],                     // min then max
        vec![100, 30],                     // max then min
        vec![50, 50, 50, 50],             // constant
        vec![30, 30, 30, 30, 30],         // all min
        vec![100, 100, 100, 100, 100],    // all max
        vec![100, 90, 80, 70, 60, 50, 40, 30], // strictly decreasing
        vec![30, 40, 50, 60, 70, 80, 90, 100], // strictly increasing
        vec![30, 100, 30, 100, 30],       // alternating min/max
        vec![50, 50, 50, 51],             // constant then bump
        vec![99, 100, 30, 31],            // near boundaries
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

    // Apply every mutation to every seed
    for seed_arr in &seeds {
        for &mk in &mutation_kinds {
            emit(mutate(seed_arr.clone(), mk), &mut seen, &mut out, &mut count);
        }
    }

    // Size classes with random mutations
    let size_classes: Vec<(usize, usize)> = vec![
        (1, 5),        // tiny
        (6, 20),       // small
        (21, 100),     // medium
        (101, 1000),   // large
        (1001, 10000), // very large
    ];

    for &(lo, hi) in &size_classes {
        for _ in 0..6 {
            if count >= target { break; }
            let len = rng.gen_range_usize(lo, hi);
            let temps = random_temps(&mut rng, len);
            let mk = rng.gen_range_usize(0, 10) as u8;
            emit(mutate(temps, mk), &mut seen, &mut out, &mut count);
        }
    }

    // Fill remaining with random seeds
    while count < target {
        let len = match count % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(1, 20),
            2 => rng.gen_range_usize(21, 100),
            3 => rng.gen_range_usize(101, 1000),
            _ => rng.gen_range_usize(1001, 10000),
        };
        let temps = random_temps(&mut rng, len);
        let mk = rng.gen_range_usize(0, 10) as u8;
        emit(mutate(temps, mk), &mut seen, &mut out, &mut count);
    }
}
