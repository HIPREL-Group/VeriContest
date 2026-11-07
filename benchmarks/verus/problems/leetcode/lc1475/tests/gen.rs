use vstd::prelude::*;

verus! {

pub fn generate_test_case(prices: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= prices.len() <= 500,
        forall|i: int| 0 <= i < prices.len() ==> 1 <= #[trigger] prices[i] <= 1000,
    ensures
        1 <= result.len() <= 500,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 1000,
{
    if mutation_kind == 0 {
        // identity
        prices
    } else if mutation_kind == 1 {
        // set last element to 1 (min boundary)
        let mut p = prices;
        let last = p.len() - 1;
        p.set(last, 1);
        p
    } else if mutation_kind == 2 {
        // set last element to 1000 (max boundary)
        let mut p = prices;
        let last = p.len() - 1;
        p.set(last, 1000);
        p
    } else if mutation_kind == 3 {
        // set all elements to one value (the first element)
        let val = prices[0];
        let mut p = prices;
        let mut i: usize = 0;
        while i < p.len()
            invariant
                0 <= i <= p.len(),
                p.len() == prices.len(),
                1 <= p.len() <= 500,
                1 <= val <= 1000,
                forall|j: int| 0 <= j < i ==> p[j] == val,
                forall|j: int| i <= j < p.len() ==> p[j] == prices[j],
                forall|j: int| 0 <= j < i ==> 1 <= #[trigger] p[j] <= 1000,
                forall|j: int| i <= j < p.len() ==> 1 <= #[trigger] p[j] <= 1000,
            decreases p.len() - i,
        {
            p.set(i, val);
            i += 1;
        }
        p
    } else if mutation_kind == 4 && prices.len() < 500 {
        // grow: append element equal to first
        let mut p = prices;
        p.push(p[0]);
        p
    } else if mutation_kind == 5 && prices.len() > 1 {
        // shrink: pop last element
        let mut p = prices;
        p.pop();
        p
    } else if mutation_kind == 6 {
        // nudge first element up: if < 1000, increment
        let mut p = prices;
        if p[0] < 1000 {
            p.set(0, p[0] + 1);
        }
        p
    } else if mutation_kind == 7 {
        // nudge first element down: if > 1, decrement
        let mut p = prices;
        if p[0] > 1 {
            p.set(0, p[0] - 1);
        }
        p
    } else if mutation_kind == 8 && prices.len() >= 2 {
        // swap first two elements
        let mut p = prices;
        let tmp = p[0];
        p.set(0, p[1]);
        p.set(1, tmp);
        p
    } else {
        // fallback: identity
        prices
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

fn mutate(prices: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(prices, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_prices(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut prices = Vec::with_capacity(len);
    for _ in 0..len {
        prices.push(rng.gen_range_i64(1, 1000) as i32);
    }
    prices
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1475);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |prices: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        let key = format!("{:?}", prices);
        if !seen.insert(key) { return; }
        let output = Solution::final_prices(prices.clone());
        writeln!(out, "{}", json!({"input": {"prices": prices}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![8, 4, 6, 2, 3],
        vec![1, 2, 3, 4, 5],
        vec![10, 1, 1, 6],
    ];

    // Hand-crafted seeds
    let seeds: Vec<Vec<i32>> = vec![
        vec![1],
        vec![1000],
        vec![1, 1],
        vec![1000, 1000],
        vec![5, 3, 1],
        vec![1, 3, 5],
        vec![500, 500, 500],
        vec![1, 1000, 1, 1000],
        vec![10, 9, 8, 7, 6, 5, 4, 3, 2, 1],
        vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
        vec![3, 3, 3, 3, 3],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8];

    // Emit examples with identity mutation
    for ex in &examples {
        emit(mutate(ex.clone(), 0), &mut seen, &mut out, &mut count);
    }

    // Apply every mutation to every seed
    for s in &seeds {
        for &mk in &mutation_kinds {
            let result = mutate(s.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds with random mutations, diverse size classes
    for i in 0..80 {
        let len = match i % 5 {
            0 => rng.gen_range_usize(1, 5),     // tiny
            1 => rng.gen_range_usize(1, 10),    // small
            2 => rng.gen_range_usize(11, 50),   // medium
            3 => rng.gen_range_usize(51, 200),  // large
            _ => rng.gen_range_usize(201, 500), // max
        };
        let s = random_prices(&mut rng, len);
        let mk = rng.gen_range_usize(0, 8) as u8;
        let result = mutate(s, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }

    // Fill remaining with random seeds, identity mutation
    while count < target {
        let len = rng.gen_range_usize(1, 500);
        let s = random_prices(&mut rng, len);
        emit(mutate(s, 0), &mut seen, &mut out, &mut count);
    }
}
