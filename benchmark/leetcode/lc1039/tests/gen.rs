use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        3 <= values.len() <= 50,
        forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 100,
    ensures
        3 <= result.len() <= 50,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 100,
{
    if mutation_kind == 0 {
        // identity
        values
    } else if mutation_kind == 1 {
        // set last element to 1 (min boundary)
        let mut v = values;
        let last = v.len() - 1;
        v.set(last, 1);
        v
    } else if mutation_kind == 2 {
        // set last element to 100 (max boundary)
        let mut v = values;
        let last = v.len() - 1;
        v.set(last, 100);
        v
    } else if mutation_kind == 3 {
        // set all elements to 1
        let mut v = values;
        let mut i: usize = 0;
        while i < v.len()
            invariant
                0 <= i <= v.len(),
                v.len() == values.len(),
                3 <= v.len() <= 50,
                forall|j: int| 0 <= j < i ==> v[j] == 1i32,
                forall|j: int| i <= j < v.len() ==> v[j] == values[j],
            decreases v.len() - i,
        {
            v.set(i, 1);
            i += 1;
        }
        v
    } else if mutation_kind == 4 {
        // set all elements to 100
        let mut v = values;
        let mut i: usize = 0;
        while i < v.len()
            invariant
                0 <= i <= v.len(),
                v.len() == values.len(),
                3 <= v.len() <= 50,
                forall|j: int| 0 <= j < i ==> v[j] == 100i32,
                forall|j: int| i <= j < v.len() ==> v[j] == values[j],
            decreases v.len() - i,
        {
            v.set(i, 100);
            i += 1;
        }
        v
    } else if mutation_kind == 5 && values.len() < 50 {
        // grow: append element 1
        let mut v = values;
        v.push(1);
        v
    } else if mutation_kind == 6 && values.len() > 3 {
        // shrink: remove last element
        let mut v = values;
        v.pop();
        v
    } else if mutation_kind == 7 {
        // nudge first element up (if < 100)
        let mut v = values;
        if v[0] < 100 {
            v.set(0, v[0] + 1);
        }
        v
    } else if mutation_kind == 8 {
        // nudge first element down (if > 1)
        let mut v = values;
        if v[0] > 1 {
            v.set(0, v[0] - 1);
        }
        v
    } else if mutation_kind == 9 {
        // set first element to same as last (duplicate boundary values)
        let mut v = values;
        let last_val = v[v.len() - 1];
        v.set(0, last_val);
        v
    } else {
        values // fallback
    }
}

} // verus!

extern crate serde_json;
use serde_json::json;

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
        vals.push(rng.gen_range_i64(1, 100) as i32);
    }
    vals
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1039);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |values: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize, target_count: usize| {
        if *count >= target_count { return; }
        let key = format!("{:?}", values);
        if !seen.insert(key) { return; }
        let output = Solution::min_score_triangulation(values.clone());
        writeln!(out, "{}", json!({"input": {"values": values}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description
    let examples: Vec<Vec<i32>> = vec![
        vec![1, 2, 3],
        vec![3, 7, 4, 5],
        vec![1, 3, 1, 4, 1, 5],
    ];
    for ex in &examples {
        emit(ex.clone(), &mut seen, &mut out, &mut count, target_count);
    }

    // Interesting seed arrays
    let seeds: Vec<Vec<i32>> = vec![
        vec![1, 1, 1],
        vec![100, 100, 100],
        vec![1, 100, 1],
        vec![100, 1, 100],
        vec![1, 1, 1, 1, 1],
        vec![50, 50, 50],
        vec![1, 2, 3, 4, 5],
        vec![100, 99, 98],
        vec![1, 50, 100],
        vec![10, 20, 30, 40, 50],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    // Apply every mutation to every seed
    for s in &seeds {
        for &mk in &mutation_kinds {
            let result = generate_test_case(s.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count, target_count);
        }
    }

    // Diverse size classes with random mutations
    for i in 0..60 {
        if count >= target_count { break; }
        let len = match i % 5 {
            0 => rng.gen_range_usize(3, 5),       // tiny
            1 => rng.gen_range_usize(3, 10),      // small
            2 => rng.gen_range_usize(11, 25),     // medium
            3 => rng.gen_range_usize(26, 40),     // large
            _ => rng.gen_range_usize(41, 50),     // max
        };
        let s = random_values(&mut rng, len);
        let mk = rng.gen_range_usize(0, 9) as u8;
        let result = generate_test_case(s, mk);
        emit(result, &mut seen, &mut out, &mut count, target_count);
    }

    // Fill remaining with random arrays, identity mutation
    while count < target_count {
        let len = rng.gen_range_usize(3, 50);
        let s = random_values(&mut rng, len);
        emit(generate_test_case(s, 0), &mut seen, &mut out, &mut count, target_count);
    }
}
