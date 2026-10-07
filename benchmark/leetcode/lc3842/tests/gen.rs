use vstd::prelude::*;

verus! {

pub fn generate_test_case(bulbs: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= bulbs.len() <= 100,
        forall|i: int| 0 <= i < bulbs.len() ==> 1 <= #[trigger] bulbs[i] <= 100,
    ensures
        1 <= result.len() <= 100,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 100,
{
    if mutation_kind == 0 {
        // identity
        bulbs
    } else if mutation_kind == 1 {
        // set last element to 1 (min boundary)
        let mut b = bulbs;
        let last = b.len() - 1;
        b.set(last, 1);
        b
    } else if mutation_kind == 2 {
        // set last element to 100 (max boundary)
        let mut b = bulbs;
        let last = b.len() - 1;
        b.set(last, 100);
        b
    } else if mutation_kind == 3 && bulbs.len() < 100 {
        // grow by one element (push 50)
        let mut b = bulbs;
        b.push(50);
        b
    } else if mutation_kind == 4 && bulbs.len() > 1 {
        // shrink by one element (pop)
        let mut b = bulbs;
        b.pop();
        b
    } else if mutation_kind == 5 {
        // set all elements to same value (all toggle same bulb)
        let mut b = bulbs;
        let mut i: usize = 0;
        while i < b.len()
            invariant
                0 <= i <= b.len(),
                b.len() == bulbs.len(),
                1 <= b.len() <= 100,
                forall|j: int| 0 <= j < i ==> b[j] == 42,
                forall|j: int| i <= j < b.len() ==> b[j] == bulbs[j],
            decreases b.len() - i,
        {
            b.set(i, 42);
            i += 1;
        }
        b
    } else if mutation_kind == 6 {
        // nudge first element up: if < 100, increment
        let mut b = bulbs;
        if b[0] < 100 {
            b.set(0, b[0] + 1);
        }
        b
    } else if mutation_kind == 7 {
        // nudge first element down: if > 1, decrement
        let mut b = bulbs;
        if b[0] > 1 {
            b.set(0, b[0] - 1);
        }
        b
    } else if mutation_kind == 8 && bulbs.len() >= 2 {
        // swap first two elements
        let mut b = bulbs;
        let tmp = b[0];
        b.set(0, b[1]);
        b.set(1, tmp);
        b
    } else if mutation_kind == 9 {
        // set first element to same as last (duplicate toggle)
        let mut b = bulbs;
        let last_val = b[b.len() - 1];
        b.set(0, last_val);
        b
    } else {
        // fallback
        bulbs
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

fn random_bulbs(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut bulbs = Vec::with_capacity(len);
    for _ in 0..len {
        bulbs.push(rng.gen_range_i64(1, 100) as i32);
    }
    bulbs
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(3842);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut emitted = 0usize;

    let mut emit = |bulbs: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, emitted: &mut usize| {
        if *emitted >= count { return; }
        let key = format!("{:?}", bulbs);
        if !seen.insert(key) { return; }
        let output = Solution::toggle_light_bulbs(bulbs.clone());
        writeln!(out, "{}", json!({"input": {"bulbs": bulbs}, "output": output})).unwrap();
        *emitted += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![10, 30, 20, 10],
        vec![100, 100],
    ];
    for ex in examples {
        emit(ex, &mut seen, &mut out, &mut emitted);
    }

    // Boundary/special seed inputs
    let seeds: Vec<Vec<i32>> = vec![
        vec![1],
        vec![100],
        vec![1, 1],
        vec![50, 50, 50],
        vec![1, 2, 3, 4, 5],
        vec![100, 99, 98, 97, 96],
        vec![42; 100],
        vec![1; 1],
        vec![50],
    ];
    for s in seeds {
        for mk in 0..10u8 {
            let mutated = generate_test_case(s.clone(), mk);
            emit(mutated, &mut seen, &mut out, &mut emitted);
        }
    }

    // Random inputs with size classes and mutations
    while emitted < count {
        let n = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 3),    // tiny
            1 => rng.gen_range_usize(1, 10),   // small
            2 => rng.gen_range_usize(11, 50),  // medium
            3 => rng.gen_range_usize(51, 100), // large
            _ => 100,                           // max
        };
        let bulbs = random_bulbs(&mut rng, n);
        let mk = rng.gen_range_usize(0, 9) as u8;
        let mutated = generate_test_case(bulbs, mk);
        emit(mutated, &mut seen, &mut out, &mut emitted);
    }
}
