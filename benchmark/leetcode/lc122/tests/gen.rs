use vstd::prelude::*;

verus! {

pub fn generate_test_case(prices: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= prices.len() <= 30_000,
        forall|i: int| 0 <= i < prices.len() ==> 0 <= #[trigger] prices[i] <= 10_000,
    ensures
        1 <= result.len() <= 30_000,
        forall|i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] <= 10_000,
{
    if mutation_kind == 0 {
        // identity
        prices
    } else if mutation_kind == 1 {
        // set last element to 0
        let mut p = prices;
        let last = p.len() - 1;
        p.set(last, 0);
        p
    } else if mutation_kind == 2 {
        // set last element to 10_000 (max boundary)
        let mut p = prices;
        let last = p.len() - 1;
        p.set(last, 10_000);
        p
    } else if mutation_kind == 3 {
        // set first element to 0
        let mut p = prices;
        p.set(0, 0);
        p
    } else if mutation_kind == 4 {
        // set first element to 10_000
        let mut p = prices;
        p.set(0, 10_000);
        p
    } else if mutation_kind == 5 && prices.len() < 30_000 {
        // grow: push a 0
        let mut p = prices;
        p.push(0);
        p
    } else if mutation_kind == 6 && prices.len() > 1 {
        // shrink: pop last element
        let mut p = prices;
        p.pop();
        p
    } else if mutation_kind == 7 {
        // nudge last element up (if < 10_000)
        let mut p = prices;
        let last = p.len() - 1;
        if p[last] < 10_000 {
            p.set(last, p[last] + 1);
        }
        p
    } else if mutation_kind == 8 {
        // nudge last element down (if > 0)
        let mut p = prices;
        let last = p.len() - 1;
        if p[last] > 0 {
            p.set(last, p[last] - 1);
        }
        p
    } else if mutation_kind == 9 {
        // set all elements to 0
        let mut p = prices;
        let mut i: usize = 0;
        while i < p.len()
            invariant
                0 <= i <= p.len(),
                p.len() == prices.len(),
                1 <= p.len() <= 30_000,
                forall|j: int| 0 <= j < i ==> p[j] == 0i32,
                forall|j: int| i <= j < p.len() ==> p[j] == prices[j],
            decreases p.len() - i,
        {
            p.set(i, 0);
            i += 1;
        }
        p
    } else if mutation_kind == 10 {
        // set all elements to 10_000
        let mut p = prices;
        let mut i: usize = 0;
        while i < p.len()
            invariant
                0 <= i <= p.len(),
                p.len() == prices.len(),
                1 <= p.len() <= 30_000,
                forall|j: int| 0 <= j < i ==> p[j] == 10_000i32,
                forall|j: int| i <= j < p.len() ==> p[j] == prices[j],
            decreases p.len() - i,
        {
            p.set(i, 10_000);
            i += 1;
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

fn random_prices(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut prices = Vec::with_capacity(len);
    for _ in 0..len {
        prices.push(rng.gen_range_i64(0, 10_000) as i32);
    }
    prices
}

fn mutate(prices: Vec<i32>, mk: u8) -> Vec<i32> {
    generate_test_case(prices, mk)
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
        vec![7, 1, 5, 3, 6, 4],
        vec![1, 2, 3, 4, 5],
        vec![7, 6, 4, 3, 1],
    ];
    for s in &example_seeds {
        emit(s.clone(), &mut seen, &mut out, &mut count);
    }

    // Interesting seed arrays
    let fixed_seeds: Vec<Vec<i32>> = vec![
        vec![0],
        vec![10_000],
        vec![5000],
        vec![0, 0],
        vec![0, 10_000],
        vec![10_000, 0],
        vec![1, 1, 1, 1, 1],
        vec![0, 1, 2, 3, 4],
        vec![4, 3, 2, 1, 0],
        vec![1, 10_000, 1, 10_000],
        vec![5000, 5000, 5000],
    ];

    let mutation_kinds: Vec<u8> = (0..=10).collect();

    // Apply every mutation to every seed
    for s in &fixed_seeds {
        for &mk in &mutation_kinds {
            emit(mutate(s.clone(), mk), &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds with random mutations across size classes
    while count < target {
        let len = match count % 5 {
            0 => rng.gen_range_usize(1, 5),        // tiny
            1 => rng.gen_range_usize(1, 10),       // small
            2 => rng.gen_range_usize(11, 100),     // medium
            3 => rng.gen_range_usize(101, 1000),   // large
            _ => rng.gen_range_usize(1001, 5000),  // big
        };
        let prices = random_prices(&mut rng, len);
        let mk = rng.gen_range_usize(0, 10) as u8;
        emit(mutate(prices, mk), &mut seen, &mut out, &mut count);
    }
}
