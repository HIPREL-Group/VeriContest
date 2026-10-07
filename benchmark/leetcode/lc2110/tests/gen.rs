use vstd::prelude::*;

verus! {

pub fn generate_test_case(prices: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= prices.len() <= 100_000,
        forall|i: int| 0 <= i < prices.len() ==> 1 <= #[trigger] prices[i] <= 100_000,
    ensures
        1 <= result.len() <= 100_000,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 100_000,
{
    if mutation_kind == 0 {
        prices
    } else if mutation_kind == 1 {
        let mut p = prices;
        let last = p.len() - 1;
        p.set(last, 1);
        p
    } else if mutation_kind == 2 {
        let mut p = prices;
        let last = p.len() - 1;
        p.set(last, 100_000);
        p
    } else if mutation_kind == 3 && prices.len() < 100_000 {
        let mut p = prices;
        p.push(1);
        p
    } else if mutation_kind == 4 && prices.len() > 1 {
        let mut p = prices;
        p.pop();
        p
    } else if mutation_kind == 5 {
        let mut p = prices;
        let mut i: usize = 0;
        while i < p.len()
            invariant
                0 <= i <= p.len(),
                p.len() == prices.len(),
                1 <= p.len() <= 100_000,
                forall|j: int| 0 <= j < i ==> p[j] == 1i32,
                forall|j: int| i <= j < p.len() ==> p[j] == prices[j],
            decreases p.len() - i,
        {
            p.set(i, 1);
            i += 1;
        }
        p
    } else if mutation_kind == 6 {
        let mut p = prices;
        let last = p.len() - 1;
        if p[last] < 100_000 {
            p.set(last, p[last] + 1);
        }
        p
    } else if mutation_kind == 7 {
        let mut p = prices;
        let last = p.len() - 1;
        if p[last] > 1 {
            p.set(last, p[last] - 1);
        }
        p
    } else if mutation_kind == 8 && prices.len() >= 2 {
        let mut p = prices;
        let last = p.len() - 1;
        let tmp = p[0];
        p.set(0, p[last]);
        p.set(last, tmp);
        p
    } else if mutation_kind == 9 {
        let mut p = prices;
        let start = p[0];
        let mut i: usize = 1;
        while i < p.len()
            invariant
                1 <= i <= p.len(),
                p.len() == prices.len(),
                1 <= p.len() <= 100_000,
                p[0] == start,
                1 <= start <= 100_000i32,
                forall|j: int| 1 <= j < i ==> p[j] == (
                    if start - j as i32 >= 1 { start - j as i32 } else { 1 }
                ),
                forall|j: int| i <= j < p.len() ==> p[j] == prices[j],
            decreases p.len() - i,
        {
            let val = if start - i as i32 >= 1 { start - i as i32 } else { 1 };
            p.set(i, val);
            i += 1;
        }
        p
    } else {
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

include!("../code.rs");

fn mutate(prices: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(prices, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_prices(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut prices = Vec::with_capacity(len);
    for _ in 0..len {
        prices.push(rng.gen_range_i64(1, 100_000) as i32);
    }
    prices
}

fn descent_prices(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut prices = Vec::with_capacity(len);
    let start = rng.gen_range_i64(len as i64, 100_000) as i32;
    for i in 0..len {
        let val = start - i as i32;
        prices.push(if val >= 1 { val } else { 1 });
    }
    prices
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2110);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |prices: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count {
            return;
        }
        let key = format!("{:?}", prices);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::get_descent_periods(prices.clone());
        writeln!(out, "{}", json!({"input": {"prices": prices}, "output": output})).unwrap();
        *count += 1;
    };

    let example_seeds: Vec<Vec<i32>> = vec![
        vec![3, 2, 1, 4],
        vec![8, 6, 7, 7],
        vec![1],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    for seed_prices in &example_seeds {
        for &mk in &mutation_kinds {
            let result = mutate(seed_prices.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    let special_seeds: Vec<Vec<i32>> = vec![
        vec![5, 5, 5, 5, 5],
        vec![5, 4, 3, 2, 1],
        vec![10, 9, 8, 7, 6, 5, 4, 3, 2, 1],
        vec![3, 2, 5, 4, 3, 8, 7],
        vec![100_000, 99_999, 99_998],
        vec![1, 1, 1],
        vec![2, 1, 2, 1, 2, 1],
        vec![100_000],
        vec![1, 2, 3, 4, 5],
    ];

    for seed_prices in &special_seeds {
        for &mk in &mutation_kinds {
            let result = mutate(seed_prices.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    while count < target_count {
        let len = match count % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 1000),
            _ => rng.gen_range_usize(1001, 10000),
        };

        let prices = if count % 3 == 0 {
            descent_prices(&mut rng, len)
        } else {
            random_prices(&mut rng, len)
        };

        let mk = rng.gen_range_usize(0, 9) as u8;
        let result = mutate(prices, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }
}
