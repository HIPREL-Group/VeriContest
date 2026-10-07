use vstd::prelude::*;

verus! {

pub fn generate_test_case(base_prices: Vec<i32>, money: i32, mutation_kind: u8) -> (prices: Vec<i32>)
    requires
        2 <= base_prices.len() <= 50,
        forall|i: int| 0 <= i < base_prices.len() ==> 1 <= #[trigger] base_prices[i] <= 100,
        1 <= money <= 100,
    ensures
        2 <= prices.len() <= 50,
        forall|i: int| 0 <= i < prices.len() ==> 1 <= #[trigger] prices[i] <= 100,
        1 <= money <= 100,
{
    if mutation_kind == 0 {
        base_prices
    } else if mutation_kind == 1 {
        let mut p = base_prices;
        p.set(0, 1);
        p
    } else if mutation_kind == 2 {
        let mut p = base_prices;
        p.set(0, 100);
        p
    } else if mutation_kind == 3 {
        let mut p = base_prices;
        let mut i: usize = 0;
        while i < p.len()
            invariant
                0 <= i <= p.len(),
                p.len() == base_prices.len(),
                2 <= p.len() <= 50,
                forall|j: int| 0 <= j < i ==> p[j] == 1i32,
                forall|j: int| i <= j < p.len() ==> p[j] == base_prices[j],
            decreases p.len() - i,
        {
            p.set(i, 1);
            i += 1;
        }
        p
    } else if mutation_kind == 4 {
        let mut p = base_prices;
        let mut i: usize = 0;
        while i < p.len()
            invariant
                0 <= i <= p.len(),
                p.len() == base_prices.len(),
                2 <= p.len() <= 50,
                forall|j: int| 0 <= j < i ==> p[j] == 100i32,
                forall|j: int| i <= j < p.len() ==> p[j] == base_prices[j],
            decreases p.len() - i,
        {
            p.set(i, 100);
            i += 1;
        }
        p
    } else if mutation_kind == 5 && base_prices.len() < 50 {
        let mut p = base_prices;
        p.push(1);
        p
    } else if mutation_kind == 6 && base_prices.len() > 2 {
        let mut p = base_prices;
        p.pop();
        p
    } else if mutation_kind == 7 {
        let mut p = base_prices;
        let last = p.len() - 1;
        if p[last] < 100 {
            p.set(last, p[last] + 1);
        }
        p
    } else if mutation_kind == 8 {
        let mut p = base_prices;
        let last = p.len() - 1;
        if p[last] > 1 {
            p.set(last, p[last] - 1);
        }
        p
    } else if mutation_kind == 9 && base_prices.len() >= 2 {
        let mut p = base_prices;
        let last = p.len() - 1;
        let tmp = p[0];
        p.set(0, p[last]);
        p.set(last, tmp);
        p
    } else {
        base_prices
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

fn mutate(base_prices: Vec<i32>, money: i32, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(base_prices, money, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_prices(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut prices = Vec::with_capacity(len);
    for _ in 0..len {
        prices.push(rng.gen_range_i64(1, 100) as i32);
    }
    prices
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2706);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |prices: Vec<i32>, money: i32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count {
            return;
        }
        let key = format!("{:?}_{}", prices, money);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::buy_choco(prices.clone(), money);
        writeln!(out, "{}", json!({"input": {"prices": prices, "money": money}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    emit(vec![1, 2, 2], 3, &mut seen, &mut out, &mut count);
    emit(vec![3, 2, 3], 3, &mut seen, &mut out, &mut count);

    // Hand-crafted seeds
    let seed_prices: Vec<Vec<i32>> = vec![
        vec![1, 1],
        vec![100, 100],
        vec![1, 100],
        vec![50, 50],
        vec![1, 2, 3, 4, 5],
        vec![10, 20, 30, 40, 50],
        vec![1, 1, 1, 1, 1],
        vec![100, 100, 100, 100, 100],
        vec![99, 100],
        vec![1, 2],
    ];
    let seed_moneys: Vec<i32> = vec![1, 2, 50, 100, 3, 10, 99];
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    for sp in &seed_prices {
        for &m in &seed_moneys {
            for &mk in &mutation_kinds {
                let result = mutate(sp.clone(), m, mk);
                emit(result, m, &mut seen, &mut out, &mut count);
            }
        }
    }

    // Random seeds with random mutations across size classes
    while count < target_count {
        let n: usize = match rng.gen_range_usize(0, 4) {
            0 => 2,
            1 => rng.gen_range_usize(2, 5),
            2 => rng.gen_range_usize(6, 15),
            3 => rng.gen_range_usize(16, 35),
            _ => rng.gen_range_usize(36, 50),
        };
        let prices = random_prices(&mut rng, n);
        let money = if rng.gen_range_usize(0, 4) == 0 {
            *[1i32, 2, 100, 99].get(rng.gen_range_usize(0, 3)).unwrap()
        } else {
            rng.gen_range_i64(1, 100) as i32
        };
        let mk = rng.gen_range_usize(0, 9) as u8;
        let result = mutate(prices, money, mk);
        emit(result, money, &mut seen, &mut out, &mut count);
    }
}
