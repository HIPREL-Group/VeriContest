use vstd::prelude::*;

verus! {

pub fn generate_test_case(machines: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= machines.len() <= 10000,
        forall|i: int| 0 <= i < machines.len() ==> 0 <= #[trigger] machines[i] <= 100000,
    ensures
        1 <= result.len() <= 10000,
        forall|i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] <= 100000,
{
    if mutation_kind == 0 {
        // identity
        machines
    } else if mutation_kind == 1 {
        // set all elements to 0
        let mut m = machines;
        let mut i: usize = 0;
        while i < m.len()
            invariant
                0 <= i <= m.len(),
                m.len() == machines.len(),
                1 <= m.len() <= 10000,
                forall|j: int| 0 <= j < i ==> m[j] == 0,
                forall|j: int| i <= j < m.len() ==> 0 <= #[trigger] m[j] <= 100000,
            decreases m.len() - i,
        {
            m.set(i, 0);
            i += 1;
        }
        m
    } else if mutation_kind == 2 {
        // set all elements to same value (first element)
        let val = machines[0];
        let mut m = machines;
        let mut i: usize = 0;
        while i < m.len()
            invariant
                0 <= i <= m.len(),
                m.len() == machines.len(),
                1 <= m.len() <= 10000,
                0 <= val <= 100000,
                forall|j: int| 0 <= j < i ==> m[j] == val,
                forall|j: int| i <= j < m.len() ==> 0 <= #[trigger] m[j] <= 100000,
            decreases m.len() - i,
        {
            m.set(i, val);
            i += 1;
        }
        m
    } else if mutation_kind == 3 && machines.len() < 10000 {
        // grow: append a 0
        let mut m = machines;
        m.push(0);
        m
    } else if mutation_kind == 4 && machines.len() > 1 {
        // shrink: remove last element
        let mut m = machines;
        m.pop();
        m
    } else if mutation_kind == 5 {
        // set first element to 100000 (max boundary)
        let mut m = machines;
        m.set(0, 100000);
        m
    } else if mutation_kind == 6 {
        // set last element to 0
        let mut m = machines;
        let last = m.len() - 1;
        m.set(last, 0);
        m
    } else if mutation_kind == 7 {
        // nudge first element up: if < 100000, increment by 1
        let mut m = machines;
        if m[0] < 100000 {
            m.set(0, m[0] + 1);
        }
        m
    } else if mutation_kind == 8 {
        // nudge first element down: if > 0, decrement by 1
        let mut m = machines;
        if m[0] > 0 {
            m.set(0, m[0] - 1);
        }
        m
    } else if mutation_kind == 9 && machines.len() >= 2 {
        // swap first and last elements
        let mut m = machines;
        let last = m.len() - 1;
        let tmp = m[0];
        m.set(0, m[last]);
        m.set(last, tmp);
        m
    } else {
        machines // fallback
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

fn mutate(machines: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(machines, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_machines(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut machines = Vec::with_capacity(len);
    for _ in 0..len {
        machines.push(rng.gen_range_i64(0, 100000) as i32);
    }
    machines
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(517);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |machines: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target {
            return;
        }
        let key = format!("{:?}", machines);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::find_min_moves(machines.clone());
        writeln!(out, "{}", json!({"input": {"machines": machines}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![1, 0, 5],
        vec![0, 3, 0],
        vec![0, 2, 0],
    ];
    for ex in &examples {
        emit(ex.clone(), &mut seen, &mut out, &mut count);
    }

    // Curated seeds: edge cases
    let seeds: Vec<Vec<i32>> = vec![
        vec![0],
        vec![100000],
        vec![0, 0],
        vec![1, 1],
        vec![0, 0, 0],
        vec![5, 5, 5],
        vec![100000, 0],
        vec![0, 100000],
        vec![50000, 50000],
        vec![3, 0, 0, 0],
        vec![0, 0, 0, 3],
        vec![10, 0, 10, 0, 10],
        vec![0, 0, 0, 0, 0],
        vec![4, 0, 0, 0, 0],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    // Apply every mutation to every seed
    for s in &seeds {
        for &mk in &mutation_kinds {
            emit(mutate(s.clone(), mk), &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds with diverse sizes and random mutations
    let size_classes: Vec<(usize, usize)> = vec![
        (1, 3),       // tiny
        (4, 10),      // small
        (11, 100),    // medium
        (101, 1000),  // large
        (1001, 10000),// max
    ];

    for (lo, hi) in &size_classes {
        for _ in 0..12 {
            let len = rng.gen_range_usize(*lo, *hi);
            let seed_machines = random_machines(&mut rng, len);
            let mk = rng.gen_range_usize(0, 9) as u8;
            emit(mutate(seed_machines, mk), &mut seen, &mut out, &mut count);
        }
    }

    // Fill remaining with random seeds, identity mutation
    while count < target {
        let len = match count % 5 {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(4, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 1000),
            _ => rng.gen_range_usize(1001, 10000),
        };
        let seed_machines = random_machines(&mut rng, len);
        emit(mutate(seed_machines, 0), &mut seen, &mut out, &mut count);
    }
}
