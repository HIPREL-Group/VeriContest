use vstd::prelude::*;

verus! {

pub fn generate_test_case(prices: Vec<i32>, fee: i32, mutation_kind: u8) -> (result: (Vec<i32>, i32))
    requires
        1 <= prices.len() <= 50_000,
        forall|i: int| 0 <= i < prices.len() ==> 1 <= #[trigger] prices[i] < 50_000,
        0 <= fee < 50_000,
    ensures
        1 <= result.0.len() <= 50_000,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] < 50_000,
        0 <= result.1 < 50_000,
{
    if mutation_kind == 0 {
        // identity
        (prices, fee)
    } else if mutation_kind == 1 {
        // nudge last price up
        let mut p = prices;
        let last = p.len() - 1;
        if p[last] < 49_999 {
            p.set(last, p[last] + 1);
        }
        (p, fee)
    } else if mutation_kind == 2 {
        // nudge last price down
        let mut p = prices;
        let last = p.len() - 1;
        if p[last] > 1 {
            p.set(last, p[last] - 1);
        }
        (p, fee)
    } else if mutation_kind == 3 {
        // set all prices to 1 (constant low prices)
        let mut p = prices;
        let mut i: usize = 0;
        while i < p.len()
            invariant
                0 <= i <= p.len(),
                p.len() == prices.len(),
                1 <= p.len() <= 50_000,
                forall|j: int| 0 <= j < i ==> p[j] == 1i32,
                forall|j: int| i <= j < p.len() ==> p[j] == prices[j],
            decreases p.len() - i,
        {
            p.set(i, 1);
            i += 1;
        }
        (p, fee)
    } else if mutation_kind == 4 && prices.len() < 50_000 {
        // grow: push a valid price element
        let mut p = prices;
        p.push(1);
        (p, fee)
    } else if mutation_kind == 5 && prices.len() > 1 {
        // shrink: pop last element
        let mut p = prices;
        p.pop();
        (p, fee)
    } else if mutation_kind == 6 {
        // set fee to 0
        (prices, 0)
    } else if mutation_kind == 7 {
        // set fee to max boundary (49999)
        (prices, 49_999)
    } else if mutation_kind == 8 && prices.len() >= 2 {
        // swap first and last price
        let mut p = prices;
        let last = p.len() - 1;
        let first_val = p[0];
        let last_val = p[last];
        p.set(0, last_val);
        if last > 0 {
            p.set(last, first_val);
        }
        (p, fee)
    } else if mutation_kind == 9 {
        // nudge fee up
        if fee < 49_999 {
            (prices, fee + 1)
        } else {
            (prices, fee)
        }
    } else if mutation_kind == 10 {
        // nudge fee down
        if fee > 0 {
            (prices, fee - 1)
        } else {
            (prices, fee)
        }
    } else if mutation_kind == 11 {
        // set last price to max boundary (49999)
        let mut p = prices;
        let last = p.len() - 1;
        p.set(last, 49_999);
        (p, fee)
    } else if mutation_kind == 12 {
        // set last price to min boundary (1)
        let mut p = prices;
        let last = p.len() - 1;
        p.set(last, 1);
        (p, fee)
    } else {
        // fallback: identity
        (prices, fee)
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
        prices.push(rng.gen_range_i64(1, 49_999) as i32);
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
    let num_mutations: u8 = 13;

    let mut emit = |prices: Vec<i32>, fee: i32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target {
            return;
        }
        let key = format!("{:?}_{}", prices, fee);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::max_profit(prices.clone(), fee);
        writeln!(out, "{}", json!({
            "input": {"prices": prices, "fee": fee},
            "output": output
        })).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let example_inputs: Vec<(Vec<i32>, i32)> = vec![
        (vec![1, 3, 2, 8, 4, 9], 2),
        (vec![1, 3, 7, 5, 10, 3], 3),
    ];
    for (prices, fee) in &example_inputs {
        emit(prices.clone(), *fee, &mut seen, &mut out, &mut count);
    }

    // Seed pool: diverse price arrays + fee values
    let seed_prices: Vec<Vec<i32>> = vec![
        vec![1],
        vec![1, 2],
        vec![49_999],
        vec![1, 1, 1, 1],
        vec![1, 49_999],
        vec![49_999, 1],
        vec![1, 2, 3, 4, 5],
        vec![5, 4, 3, 2, 1],
        vec![1, 5, 1, 5, 1, 5],
        vec![100, 200, 150, 300, 250, 400],
        vec![1, 1],
        vec![10_000, 20_000, 30_000],
    ];
    let seed_fees: Vec<i32> = vec![0, 1, 2, 100, 49_999];

    // Apply every mutation to every seed combination
    for prices in &seed_prices {
        for &fee in &seed_fees {
            for mk in 0..num_mutations {
                if count >= target { break; }
                let (p, f) = generate_test_case(prices.clone(), fee, mk);
                emit(p, f, &mut seen, &mut out, &mut count);
            }
        }
    }

    // Random seeds with random mutations across size classes
    while count < target {
        let n: usize = match rng.next_u64() % 5 {
            0 => rng.gen_range_usize(1, 5),        // tiny
            1 => rng.gen_range_usize(1, 10),       // small
            2 => rng.gen_range_usize(11, 100),     // medium
            3 => rng.gen_range_usize(101, 1000),   // large
            _ => rng.gen_range_usize(1001, 50_000),// max
        };
        let prices = random_prices(&mut rng, n);
        let fee = if rng.next_u64() % 5 == 0 {
            *[0i32, 1, 49_999].get((rng.next_u64() % 3) as usize).unwrap()
        } else {
            rng.gen_range_i64(0, 49_999) as i32
        };
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let (p, f) = generate_test_case(prices, fee, mk);
        emit(p, f, &mut seen, &mut out, &mut count);
    }
}
