use vstd::prelude::*;

verus! {

pub fn generate_test_case(bp: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= bp.len() <= 100,
        forall|i: int| 0 <= i < bp.len() ==> 0 <= #[trigger] bp[i] <= 100,
    ensures
        1 <= result.len() <= 100,
        forall|i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] <= 100,
{
    if mutation_kind == 0 {
        // identity
        bp
    } else if mutation_kind == 1 {
        // set last element to 0
        let mut d = bp;
        let last = d.len() - 1;
        d.set(last, 0);
        d
    } else if mutation_kind == 2 {
        // set last element to 100
        let mut d = bp;
        let last = d.len() - 1;
        d.set(last, 100);
        d
    } else if mutation_kind == 3 {
        // set all elements to 0
        let mut d = bp;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == bp.len(),
                1 <= d.len() <= 100,
                forall|j: int| 0 <= j < i ==> d[j] == 0i32,
                forall|j: int| i <= j < d.len() ==> d[j] == bp[j],
            decreases d.len() - i,
        {
            d.set(i, 0);
            i += 1;
        }
        d
    } else if mutation_kind == 4 {
        // set all elements to 100
        let mut d = bp;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == bp.len(),
                1 <= d.len() <= 100,
                forall|j: int| 0 <= j < i ==> d[j] == 100i32,
                forall|j: int| i <= j < d.len() ==> d[j] == bp[j],
            decreases d.len() - i,
        {
            d.set(i, 100);
            i += 1;
        }
        d
    } else if mutation_kind == 5 && bp.len() < 100 {
        // grow by one element (push 0)
        let mut d = bp;
        d.push(0);
        d
    } else if mutation_kind == 6 && bp.len() > 1 {
        // shrink by one element (pop)
        let mut d = bp;
        d.pop();
        d
    } else if mutation_kind == 7 {
        // nudge last element up (if < 100)
        let mut d = bp;
        let last = d.len() - 1;
        if d[last] < 100 {
            d.set(last, d[last] + 1);
        }
        d
    } else if mutation_kind == 8 {
        // nudge last element down (if > 0)
        let mut d = bp;
        let last = d.len() - 1;
        if d[last] > 0 {
            d.set(last, d[last] - 1);
        }
        d
    } else if mutation_kind == 9 {
        // set first element to 0
        let mut d = bp;
        d.set(0, 0);
        d
    } else if mutation_kind == 10 {
        // set first element to 100
        let mut d = bp;
        d.set(0, 100);
        d
    } else {
        // fallback: identity
        bp
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

include!("../code.rs");

fn mutate(bp: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(bp, mutation_kind)
}

fn random_bp(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(0, 100) as i32);
    }
    v
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

    let mut emit = |bp: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count {
            return;
        }
        let key = format!("{:?}", bp);
        if !seen.insert(key) {
            return;
        }
        let output = count_tested_devices(bp.clone());
        writeln!(out, "{}", json!({"input": {"batteryPercentages": bp}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let example_seeds: Vec<Vec<i32>> = vec![
        vec![1, 1, 2, 1, 3],
        vec![0, 1, 2],
    ];

    // Manually crafted boundary seeds
    let boundary_seeds: Vec<Vec<i32>> = vec![
        vec![0],
        vec![100],
        vec![0, 0, 0],
        vec![100, 100, 100],
        vec![1],
        vec![50],
        vec![0, 100],
        vec![100, 0],
        vec![1, 0, 0, 0],
        vec![0, 0, 0, 1],
        vec![50, 50, 50, 50, 50],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

    // Emit examples with identity mutation first
    for seed in &example_seeds {
        emit(seed.clone(), &mut seen, &mut out, &mut count);
    }

    // Apply every mutation to every seed
    for seed in example_seeds.iter().chain(boundary_seeds.iter()) {
        for &mk in &mutation_kinds {
            let result = mutate(seed.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds across size classes with random mutations
    for i in 0..200 {
        if count >= target_count { break; }
        let len = match i % 5 {
            0 => rng.gen_range_usize(1, 3),     // tiny
            1 => rng.gen_range_usize(1, 10),    // small
            2 => rng.gen_range_usize(11, 30),   // medium
            3 => rng.gen_range_usize(31, 70),   // large
            _ => rng.gen_range_usize(71, 100),  // max
        };
        let bp = random_bp(&mut rng, len);
        let mk = rng.gen_range_usize(0, 10) as u8;
        let result = mutate(bp, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }

    // Fill remaining with random seeds, identity mutation
    while count < target_count {
        let len = rng.gen_range_usize(1, 100);
        let bp = random_bp(&mut rng, len);
        emit(mutate(bp, 0), &mut seen, &mut out, &mut count);
    }
}
