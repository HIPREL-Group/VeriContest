use vstd::prelude::*;

verus! {

pub fn generate_test_case(time: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= time.len() <= 60_000,
        forall|i: int| 0 <= i < time.len() ==> 1 <= #[trigger] time[i] <= 500,
    ensures
        1 <= result.len() <= 60_000,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 500,
{
    if mutation_kind == 0 {
        // identity
        time
    } else if mutation_kind == 1 {
        // set last element to 1 (min boundary)
        let mut t = time;
        let last = t.len() - 1;
        t.set(last, 1);
        t
    } else if mutation_kind == 2 {
        // set last element to 500 (max boundary)
        let mut t = time;
        let last = t.len() - 1;
        t.set(last, 500);
        t
    } else if mutation_kind == 3 {
        // set all elements to 60 (all pairs divisible by 60)
        let mut t = time;
        let mut i: usize = 0;
        while i < t.len()
            invariant
                0 <= i <= t.len(),
                t.len() == time.len(),
                1 <= t.len() <= 60_000,
                forall|j: int| 0 <= j < i ==> t[j] == 60,
                forall|j: int| i <= j < t.len() ==> t[j] == time[j],
            decreases t.len() - i,
        {
            t.set(i, 60);
            i += 1;
        }
        t
    } else if mutation_kind == 4 && time.len() < 60_000 {
        // grow by one element
        let mut t = time;
        t.push(1);
        t
    } else if mutation_kind == 5 && time.len() > 1 {
        // shrink by one element
        let mut t = time;
        t.pop();
        t
    } else if mutation_kind == 6 {
        // set last element to 30 (common pair: 30+30=60)
        let mut t = time;
        let last = t.len() - 1;
        t.set(last, 30);
        t
    } else if mutation_kind == 7 {
        // nudge last element: if < 500 increment, else decrement
        let mut t = time;
        let last = t.len() - 1;
        if t[last] < 500 {
            t.set(last, t[last] + 1);
        } else {
            t.set(last, t[last] - 1);
        }
        t
    } else if mutation_kind == 8 {
        // set all elements to 30 (every pair sums to 60)
        let mut t = time;
        let mut i: usize = 0;
        while i < t.len()
            invariant
                0 <= i <= t.len(),
                t.len() == time.len(),
                1 <= t.len() <= 60_000,
                forall|j: int| 0 <= j < i ==> t[j] == 30,
                forall|j: int| i <= j < t.len() ==> t[j] == time[j],
            decreases t.len() - i,
        {
            t.set(i, 30);
            i += 1;
        }
        t
    } else if mutation_kind == 9 {
        // set first element to complement of last mod 60
        let mut t = time;
        let last = t.len() - 1;
        let r = t[last] % 60;
        let comp = if r == 0 { 60i32 } else { 60 - r };
        t.set(0, comp);
        t
    } else {
        time // fallback
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

fn mutate(time: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(time, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_time_array(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut time = Vec::with_capacity(len);
    for _ in 0..len {
        time.push(rng.gen_range_i64(1, 500) as i32);
    }
    time
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |time: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count {
            return;
        }
        let key = format!("{:?}", time);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::num_pairs_divisible_by60(time.clone());
        writeln!(out, "{}", json!({"input": {"time": time}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description
    let example_seeds: Vec<Vec<i32>> = vec![
        vec![30, 20, 150, 100, 40],
        vec![60, 60, 60],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    // Apply every mutation to every example seed
    for s in &example_seeds {
        for &mk in &mutation_kinds {
            let result = mutate(s.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Hand-crafted seeds for diversity
    let extra_seeds: Vec<Vec<i32>> = vec![
        vec![1],
        vec![500],
        vec![30],
        vec![60],
        vec![1, 59],
        vec![20, 40],
        vec![30, 30, 30, 30],
        vec![1, 2, 3, 4, 5],
        vec![120, 240, 360, 480],
        vec![7, 53, 13, 47],
    ];

    for s in &extra_seeds {
        for &mk in &mutation_kinds {
            let result = mutate(s.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Diverse size classes with random mutations
    for i in 0..80 {
        if count >= target_count { break; }
        let len = match i % 5 {
            0 => rng.gen_range_usize(1, 5),        // tiny
            1 => rng.gen_range_usize(1, 10),       // small
            2 => rng.gen_range_usize(11, 100),     // medium
            3 => rng.gen_range_usize(101, 1000),   // large
            _ => rng.gen_range_usize(1001, 10000), // very large
        };
        let s = random_time_array(&mut rng, len);
        let mk = rng.gen_range_usize(0, 9) as u8;
        let result = mutate(s, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }

    // Fill remaining with random arrays, identity mutation
    while count < target_count {
        let len = rng.gen_range_usize(1, 5000);
        let s = random_time_array(&mut rng, len);
        emit(mutate(s, 0), &mut seen, &mut out, &mut count);
    }
}
