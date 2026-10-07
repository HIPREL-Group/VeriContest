use vstd::prelude::*;

verus! {

pub fn generate_test_case(piles: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        3 <= piles.len() <= 100000,
        piles.len() % 3 == 0,
        forall|i: int| 0 <= i < piles.len() ==> 1 <= #[trigger] piles[i] <= 10000,
    ensures
        3 <= result.len() <= 100000,
        result.len() % 3 == 0,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 10000,
{
    if mutation_kind == 0 {
        // identity
        piles
    } else if mutation_kind == 1 {
        // set all elements to 1 (minimum value)
        let mut p = piles;
        let mut i: usize = 0;
        while i < p.len()
            invariant
                0 <= i <= p.len(),
                p.len() == piles.len(),
                3 <= p.len() <= 100000,
                p.len() % 3 == 0,
                forall|j: int| 0 <= j < i ==> p[j] == 1,
                forall|j: int| i <= j < p.len() ==> p[j] == piles[j],
            decreases p.len() - i,
        {
            p.set(i, 1);
            i += 1;
        }
        p
    } else if mutation_kind == 2 {
        // set all elements to 10000 (maximum value)
        let mut p = piles;
        let mut i: usize = 0;
        while i < p.len()
            invariant
                0 <= i <= p.len(),
                p.len() == piles.len(),
                3 <= p.len() <= 100000,
                p.len() % 3 == 0,
                forall|j: int| 0 <= j < i ==> p[j] == 10000,
                forall|j: int| i <= j < p.len() ==> p[j] == piles[j],
            decreases p.len() - i,
        {
            p.set(i, 10000);
            i += 1;
        }
        p
    } else if mutation_kind == 3 {
        // set first element to 1 (min boundary)
        let mut p = piles;
        p.set(0, 1);
        p
    } else if mutation_kind == 4 {
        // set first element to 10000 (max boundary)
        let mut p = piles;
        p.set(0, 10000);
        p
    } else if mutation_kind == 5 {
        // set last element to 1
        let mut p = piles;
        let last = p.len() - 1;
        p.set(last, 1);
        p
    } else if mutation_kind == 6 {
        // set last element to 10000
        let mut p = piles;
        let last = p.len() - 1;
        p.set(last, 10000);
        p
    } else if mutation_kind == 7 && piles.len() <= 99997 {
        // grow by 3 elements (preserve divisibility by 3)
        let mut p = piles;
        p.push(1);
        p.push(1);
        p.push(1);
        p
    } else if mutation_kind == 8 && piles.len() > 3 {
        // shrink by 3 elements (preserve divisibility by 3)
        let mut p = piles;
        p.pop();
        p.pop();
        p.pop();
        p
    } else if mutation_kind == 9 && piles.len() >= 2 {
        // swap first two elements
        let mut p = piles;
        let a = p[0];
        let b = p[1];
        p.set(0, b);
        p.set(1, a);
        p
    } else if mutation_kind == 10 {
        // nudge first element up (if < 10000)
        let mut p = piles;
        if p[0] < 10000 {
            p.set(0, p[0] + 1);
        }
        p
    } else if mutation_kind == 11 {
        // nudge first element down (if > 1)
        let mut p = piles;
        if p[0] > 1 {
            p.set(0, p[0] - 1);
        }
        p
    } else {
        // fallback: identity
        piles
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

fn mutate(piles: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(piles, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_piles(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut piles = Vec::with_capacity(n);
    for _ in 0..n {
        piles.push(rng.gen_range_i64(1, 10000) as i32);
    }
    piles
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1561);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |piles: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target {
            return;
        }
        let key = format!("{:?}", piles);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::max_coins(piles.clone());
        writeln!(out, "{}", json!({"input": {"piles": piles}, "output": output})).unwrap();
        *count += 1;
    };

    // Example test cases from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![2, 4, 1, 2, 7, 8],
        vec![2, 4, 5],
        vec![9, 8, 7, 6, 5, 1, 2, 3, 4],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];

    // Apply every mutation to every example
    for ex in &examples {
        for &mk in &mutation_kinds {
            let result = mutate(ex.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Hand-crafted seeds
    let hand_crafted: Vec<Vec<i32>> = vec![
        vec![1, 1, 1],                         // all minimum
        vec![10000, 10000, 10000],              // all maximum
        vec![1, 10000, 5000],                   // boundary mix
        vec![1, 1, 1, 1, 1, 1],                // all same, len 6
        vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12], // ascending, len 12
    ];

    for seed_arr in &hand_crafted {
        for &mk in &mutation_kinds {
            let result = mutate(seed_arr.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Size classes for random generation
    for _ in 0..80 {
        if count >= target { break; }
        let n_raw = match rng.gen_range_usize(0, 4) {
            0 => 3,                                         // tiny (minimum)
            1 => rng.gen_range_usize(1, 3) * 3,             // small: 3,6,9
            2 => rng.gen_range_usize(4, 33) * 3,            // medium: 12..99
            3 => rng.gen_range_usize(34, 333) * 3,          // large: 102..999
            _ => rng.gen_range_usize(334, 33333) * 3,       // max: 1002..99999
        };
        let n = if n_raw > 100000 { 99999 } else { n_raw };
        let piles = random_piles(&mut rng, n);
        let mk = rng.gen_range_usize(0, 11) as u8;
        let result = mutate(piles, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }

    // Fill remaining with random piles, identity mutation
    while count < target {
        let n = rng.gen_range_usize(1, 33333) * 3;
        let n = if n > 100000 { 99999 } else { n };
        let piles = random_piles(&mut rng, n);
        emit(mutate(piles, 0), &mut seen, &mut out, &mut count);
    }
}
