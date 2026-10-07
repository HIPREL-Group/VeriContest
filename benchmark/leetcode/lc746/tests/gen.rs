use vstd::prelude::*;

verus! {

pub fn generate_test_case(cost: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        2 <= cost.len() <= 1000,
        forall|i: int| 0 <= i < cost.len() ==> 0 <= #[trigger] cost[i] <= 999,
    ensures
        2 <= result.len() <= 1000,
        forall|i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] <= 999,
{
    if mutation_kind == 0 {
        // identity
        cost
    } else if mutation_kind == 1 {
        // set last element to 0
        let mut c = cost;
        let last = c.len() - 1;
        c.set(last, 0);
        c
    } else if mutation_kind == 2 {
        // set last element to 999 (max boundary)
        let mut c = cost;
        let last = c.len() - 1;
        c.set(last, 999);
        c
    } else if mutation_kind == 3 {
        // set all elements to 0
        let mut c = cost;
        let mut i: usize = 0;
        while i < c.len()
            invariant
                0 <= i <= c.len(),
                c.len() == cost.len(),
                2 <= c.len() <= 1000,
                forall|j: int| 0 <= j < i ==> c[j] == 0,
                forall|j: int| i <= j < c.len() ==> c[j] == cost[j],
            decreases c.len() - i,
        {
            c.set(i, 0);
            i += 1;
        }
        c
    } else if mutation_kind == 4 {
        // set all elements to 999
        let mut c = cost;
        let mut i: usize = 0;
        while i < c.len()
            invariant
                0 <= i <= c.len(),
                c.len() == cost.len(),
                2 <= c.len() <= 1000,
                forall|j: int| 0 <= j < i ==> c[j] == 999,
                forall|j: int| i <= j < c.len() ==> c[j] == cost[j],
            decreases c.len() - i,
        {
            c.set(i, 999);
            i += 1;
        }
        c
    } else if mutation_kind == 5 && cost.len() < 1000 {
        // grow: push a 0
        let mut c = cost;
        c.push(0);
        c
    } else if mutation_kind == 6 && cost.len() > 2 {
        // shrink: pop last element
        let mut c = cost;
        c.pop();
        c
    } else if mutation_kind == 7 {
        // nudge last element up (if < 999)
        let mut c = cost;
        let last = c.len() - 1;
        if c[last] < 999 {
            c.set(last, c[last] + 1);
        }
        c
    } else if mutation_kind == 8 {
        // nudge last element down (if > 0)
        let mut c = cost;
        let last = c.len() - 1;
        if c[last] > 0 {
            c.set(last, c[last] - 1);
        }
        c
    } else if mutation_kind == 9 {
        // set first element to 0
        let mut c = cost;
        c.set(0, 0);
        c
    } else if mutation_kind == 10 {
        // set first element to 999
        let mut c = cost;
        c.set(0, 999);
        c
    } else if mutation_kind == 11 && cost.len() >= 2 {
        // swap first two elements
        let mut c = cost;
        let tmp = c[0];
        c.set(0, c[1]);
        c.set(1, tmp);
        c
    } else {
        // fallback: identity
        cost
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

fn mutate(cost: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(cost, mutation_kind)
}

fn random_cost_array(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut cost = Vec::with_capacity(len);
    for _ in 0..len {
        cost.push(rng.gen_range_i64(0, 999) as i32);
    }
    cost
}

extern crate serde_json;
use serde_json::json;

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

    let mut emit = |cost: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target {
            return;
        }
        let key = format!("{:?}", cost);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::min_cost_climbing_stairs(cost.clone());
        writeln!(out, "{}", json!({"input": {"cost": cost}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let example_seeds: Vec<Vec<i32>> = vec![
        vec![10, 15, 20],
        vec![1, 100, 1, 1, 1, 100, 1, 1, 100, 1],
    ];
    for s in &example_seeds {
        emit(s.clone(), &mut seen, &mut out, &mut count);
    }

    // Hand-crafted boundary seeds
    let boundary_seeds: Vec<Vec<i32>> = vec![
        vec![0, 0],                          // minimum length, all zeros
        vec![999, 999],                      // minimum length, all max
        vec![0, 999],                        // min length, mixed extremes
        vec![999, 0],                        // min length, reversed extremes
        vec![1, 1],                          // min length, all ones
        vec![0, 0, 0],                       // length 3, all zeros
        vec![999, 999, 999],                 // length 3, all max
        vec![0, 1, 0, 1, 0],                // alternating low
        vec![999, 0, 999, 0, 999],           // alternating high/low
        vec![500, 500, 500, 500],            // uniform mid
    ];
    for s in &boundary_seeds {
        emit(s.clone(), &mut seen, &mut out, &mut count);
    }

    // Apply every mutation to seeds
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];
    for s in example_seeds.iter().chain(boundary_seeds.iter()) {
        for &mk in &mutation_kinds {
            let result = mutate(s.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds with size classes + random mutations
    while count < target {
        let len: usize = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(2, 5),       // tiny
            1 => rng.gen_range_usize(2, 10),       // small
            2 => rng.gen_range_usize(11, 100),     // medium
            3 => rng.gen_range_usize(101, 500),    // large
            _ => rng.gen_range_usize(501, 1000),   // max
        };
        let seed_arr = random_cost_array(&mut rng, len);
        let mk = rng.gen_range_usize(0, 11) as u8;
        let result = mutate(seed_arr, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }
}
