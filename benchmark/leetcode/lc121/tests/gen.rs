use vstd::prelude::*;

verus! {

pub fn generate_test_case(prices: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= prices.len() <= 100_000,
        forall|i: int| 0 <= i < prices.len() ==> 0 <= #[trigger] prices[i] <= 10_000,
    ensures
        1 <= result.len() <= 100_000,
        forall|i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] <= 10_000,
{
    if mutation_kind == 0 {
        // identity
        prices
    } else if mutation_kind == 1 {
        // set first element to 0 (minimum price)
        let mut p = prices;
        p.set(0, 0);
        p
    } else if mutation_kind == 2 {
        // set first element to 10_000 (maximum price)
        let mut p = prices;
        p.set(0, 10_000);
        p
    } else if mutation_kind == 3 {
        // set last element to 0
        let mut p = prices;
        let last = p.len() - 1;
        p.set(last, 0);
        p
    } else if mutation_kind == 4 {
        // set last element to 10_000
        let mut p = prices;
        let last = p.len() - 1;
        p.set(last, 10_000);
        p
    } else if mutation_kind == 5 && prices.len() < 100_000 {
        // grow by one element (push 0)
        let mut p = prices;
        p.push(0);
        p
    } else if mutation_kind == 6 && prices.len() > 1 {
        // shrink by one element (pop)
        let mut p = prices;
        p.pop();
        p
    } else if mutation_kind == 7 {
        // set all elements to 0 (all same, no profit)
        let ghost old_prices = prices;
        let mut p = prices;
        let mut i: usize = 0;
        while i < p.len()
            invariant
                0 <= i <= p.len(),
                p.len() == old_prices.len(),
                1 <= p.len() <= 100_000,
                forall|j: int| 0 <= j < i ==> p[j] == 0,
                forall|j: int| i <= j < p.len() ==> p[j] == old_prices[j],
            decreases p.len() - i,
        {
            p.set(i, 0);
            i += 1;
        }
        p
    } else if mutation_kind == 8 {
        // nudge first element: if < 10_000, increment by 1
        let mut p = prices;
        if p[0] < 10_000 {
            p.set(0, p[0] + 1);
        }
        p
    } else if mutation_kind == 9 {
        // nudge last element down: if > 0, decrement by 1
        let mut p = prices;
        let last = p.len() - 1;
        if p[last] > 0 {
            p.set(last, p[last] - 1);
        }
        p
    } else {
        prices // fallback
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

fn random_prices(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut prices = Vec::with_capacity(len);
    for _ in 0..len {
        prices.push(rng.gen_range_i64(0, 10_000) as i32);
    }
    prices
}

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

    let mut emit = |prices: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        let key = format!("{:?}", prices);
        if !seen.insert(key) { return; }
        let output = Solution::max_profit(prices.clone());
        writeln!(out, "{}", json!({"input": {"prices": prices}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let example_seeds: Vec<Vec<i32>> = vec![
        vec![7, 1, 5, 3, 6, 4],          // Example 1: output 5
        vec![7, 6, 4, 3, 1],             // Example 2: output 0
    ];
    for seed_prices in &example_seeds {
        for mk in 0..=10u8 {
            let result = generate_test_case(seed_prices.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Interesting hand-crafted seeds
    let hand_crafted: Vec<Vec<i32>> = vec![
        vec![0],                          // single element, min price
        vec![10_000],                     // single element, max price
        vec![5_000],                      // single element, mid price
        vec![0, 10_000],                  // max possible profit
        vec![10_000, 0],                  // max possible loss (profit=0)
        vec![0, 0],                       // all zeros
        vec![10_000, 10_000],             // all max
        vec![1, 2, 3, 4, 5],             // strictly increasing
        vec![5, 4, 3, 2, 1],             // strictly decreasing
        vec![3, 3, 3, 3, 3],             // all same
        vec![1, 10_000, 0, 10_000],       // valley-peak-valley-peak
        vec![0, 0, 0, 10_000],            // flat then spike
        vec![10_000, 0, 0, 0],            // spike then flat
        vec![5_000, 0, 5_000, 0, 5_000],  // oscillating
    ];
    for seed_prices in &hand_crafted {
        for mk in 0..=10u8 {
            let result = generate_test_case(seed_prices.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds across size classes with random mutations
    while count < target {
        let n = match count % 5 {
            0 => rng.gen_range_usize(1, 5),         // tiny
            1 => rng.gen_range_usize(1, 10),        // small
            2 => rng.gen_range_usize(11, 100),      // medium
            3 => rng.gen_range_usize(101, 1000),    // large
            _ => rng.gen_range_usize(1001, 10_000), // very large
        };
        let prices = random_prices(&mut rng, n);
        let mk = rng.gen_range_usize(0, 10) as u8;
        let result = generate_test_case(prices, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }
}
