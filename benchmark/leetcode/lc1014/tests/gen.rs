use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        2 <= values.len() <= 50_000,
        forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 1000,
    ensures
        2 <= result.len() <= 50_000,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 1000,
{
    if mutation_kind == 0 {
        // identity
        values
    } else if mutation_kind == 1 {
        // set last element to max boundary (1000)
        let mut v = values;
        let last = v.len() - 1;
        v.set(last, 1000);
        v
    } else if mutation_kind == 2 {
        // set first element to min boundary (1)
        let mut v = values;
        v.set(0, 1);
        v
    } else if mutation_kind == 3 {
        // set all elements to 1 (uniform min)
        let mut v = values;
        let mut i: usize = 0;
        while i < v.len()
            invariant
                0 <= i <= v.len(),
                v.len() == values.len(),
                2 <= v.len() <= 50_000,
                forall|j: int| 0 <= j < i ==> v[j] == 1i32,
                forall|j: int| i <= j < v.len() ==> v[j] == values[j],
            decreases v.len() - i,
        {
            v.set(i, 1);
            i += 1;
        }
        v
    } else if mutation_kind == 4 && values.len() < 50_000 {
        // grow by one element
        let mut v = values;
        v.push(500);
        v
    } else if mutation_kind == 5 && values.len() > 2 {
        // shrink by one element
        let mut v = values;
        v.pop();
        v
    } else if mutation_kind == 6 {
        // nudge last element up (if < 1000, else identity)
        let mut v = values;
        let last = v.len() - 1;
        if v[last] < 1000 {
            v.set(last, (v[last] + 1) as i32);
        }
        v
    } else if mutation_kind == 7 {
        // nudge last element down (if > 1, else identity)
        let mut v = values;
        let last = v.len() - 1;
        if v[last] > 1 {
            v.set(last, (v[last] - 1) as i32);
        }
        v
    } else if mutation_kind == 8 {
        // swap first and last elements
        let mut v = values;
        let last = v.len() - 1;
        let first_val = v[0];
        let last_val = v[last];
        v.set(0, last_val);
        if last > 0 {
            v.set(last, first_val);
        }
        v
    } else if mutation_kind == 9 {
        // set all elements to 1000 (uniform max)
        let mut v = values;
        let mut i: usize = 0;
        while i < v.len()
            invariant
                0 <= i <= v.len(),
                v.len() == values.len(),
                2 <= v.len() <= 50_000,
                forall|j: int| 0 <= j < i ==> v[j] == 1000i32,
                forall|j: int| i <= j < v.len() ==> v[j] == values[j],
            decreases v.len() - i,
        {
            v.set(i, 1000);
            i += 1;
        }
        v
    } else {
        // fallback: identity
        values
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

fn random_values(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut vals = Vec::with_capacity(len);
    for _ in 0..len {
        vals.push(rng.gen_range_i64(1, 1000) as i32);
    }
    vals
}

extern crate serde_json;
use serde_json::json;

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

    let mut emit = |values: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count {
            return;
        }
        let key = format!("{:?}", values);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::max_score_sightseeing_pair(values.clone());
        writeln!(out, "{}", json!({"input": {"values": values}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![8, 1, 5, 2, 6],
        vec![1, 2],
    ];

    // Seed pool: hand-crafted interesting inputs
    let seeds: Vec<Vec<i32>> = vec![
        vec![8, 1, 5, 2, 6],       // example 1
        vec![1, 2],                 // example 2
        vec![1, 1],                 // minimal, all same min
        vec![1000, 1000],           // minimal, all same max
        vec![1, 1000],              // min then max
        vec![1000, 1],              // max then min
        vec![1, 1, 1, 1, 1],       // all ones
        vec![1000, 1000, 1000, 1000, 1000], // all max
        vec![1, 2, 3, 4, 5],       // ascending
        vec![5, 4, 3, 2, 1],       // descending
        vec![500, 500, 500],        // uniform mid
        vec![1, 1000, 1, 1000, 1],  // alternating
        vec![999, 1000],            // near-max pair
        vec![1, 2, 1000],           // spike at end
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    // Apply every mutation to every seed
    for s in &seeds {
        for &mk in &mutation_kinds {
            let result = generate_test_case(s.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Size classes with random mutations
    for i in 0..60 {
        if count >= target_count { break; }
        let len = match i % 5 {
            0 => rng.gen_range_usize(2, 5),         // tiny
            1 => rng.gen_range_usize(2, 10),        // small
            2 => rng.gen_range_usize(11, 100),      // medium
            3 => rng.gen_range_usize(101, 1000),    // large
            _ => rng.gen_range_usize(1001, 50_000), // max
        };
        let vals = random_values(&mut rng, len);
        let mk = rng.gen_range_usize(0, 9) as u8;
        let result = generate_test_case(vals, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }

    // Fill remaining with random identity
    while count < target_count {
        let len = match count % 5 {
            0 => rng.gen_range_usize(2, 5),
            1 => rng.gen_range_usize(2, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 1000),
            _ => rng.gen_range_usize(1001, 50_000),
        };
        let vals = random_values(&mut rng, len);
        emit(generate_test_case(vals, 0), &mut seen, &mut out, &mut count);
    }
}
