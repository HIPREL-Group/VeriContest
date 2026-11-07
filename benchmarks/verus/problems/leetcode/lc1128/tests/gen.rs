use vstd::prelude::*;

verus! {

pub fn generate_test_case(dominoes: Vec<Vec<i32>>, mutation_kind: u8) -> (result: Vec<Vec<i32>>)
    requires
        1 <= dominoes.len() <= 40_000,
        forall|i: int|
            0 <= i < dominoes.len() ==> (#[trigger] dominoes[i]).len() == 2,
        forall|i: int|
            0 <= i < dominoes.len() ==> 1 <= (#[trigger] dominoes[i])[0] <= 9,
        forall|i: int|
            0 <= i < dominoes.len() ==> 1 <= (#[trigger] dominoes[i])[1] <= 9,
    ensures
        1 <= result.len() <= 40_000,
        forall|i: int|
            0 <= i < result.len() ==> (#[trigger] result[i]).len() == 2,
        forall|i: int|
            0 <= i < result.len() ==> 1 <= (#[trigger] result[i])[0] <= 9,
        forall|i: int|
            0 <= i < result.len() ==> 1 <= (#[trigger] result[i])[1] <= 9,
{
    if mutation_kind == 0 {
        // identity
        dominoes
    } else if mutation_kind == 1 {
        // swap first domino's values
        let mut d = dominoes;
        let a = d[0][0];
        let b = d[0][1];
        let mut pair: Vec<i32> = Vec::new();
        pair.push(b);
        pair.push(a);
        d.set(0, pair);
        assert(d[0].len() == 2);
        assert(1 <= d[0][0] <= 9);
        assert(1 <= d[0][1] <= 9);
        d
    } else if mutation_kind == 2 {
        // set first domino to [1, 1]
        let mut d = dominoes;
        let mut pair: Vec<i32> = Vec::new();
        pair.push(1);
        pair.push(1);
        d.set(0, pair);
        d
    } else if mutation_kind == 3 {
        // set first domino to [9, 9]
        let mut d = dominoes;
        let mut pair: Vec<i32> = Vec::new();
        pair.push(9);
        pair.push(9);
        d.set(0, pair);
        d
    } else if mutation_kind == 4 && dominoes.len() < 40_000 {
        // grow: append a copy of the first domino
        let mut d = dominoes;
        let a = d[0][0];
        let b = d[0][1];
        let mut pair: Vec<i32> = Vec::new();
        pair.push(a);
        pair.push(b);
        d.push(pair);
        assert(d[d.len() - 1].len() == 2);
        d
    } else if mutation_kind == 5 && dominoes.len() > 1 {
        // shrink: remove last domino
        let mut d = dominoes;
        d.pop();
        d
    } else if mutation_kind == 6 {
        // nudge first domino's first value up (if < 9)
        let mut d = dominoes;
        let a = d[0][0];
        let b = d[0][1];
        if a < 9 {
            let mut pair: Vec<i32> = Vec::new();
            pair.push(a + 1);
            pair.push(b);
            d.set(0, pair);
        }
        d
    } else if mutation_kind == 7 {
        // nudge first domino's second value down (if > 1)
        let mut d = dominoes;
        let a = d[0][0];
        let b = d[0][1];
        if b > 1 {
            let mut pair: Vec<i32> = Vec::new();
            pair.push(a);
            pair.push(b - 1);
            d.set(0, pair);
        }
        d
    } else if mutation_kind == 8 {
        // set first domino to [1, 9]
        let mut d = dominoes;
        let mut pair: Vec<i32> = Vec::new();
        pair.push(1);
        pair.push(9);
        d.set(0, pair);
        d
    } else {
        // fallback: identity
        dominoes
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

fn mutate(dominoes: Vec<Vec<i32>>, mutation_kind: u8) -> Vec<Vec<i32>> {
    generate_test_case(dominoes, mutation_kind)
}

fn random_dominoes(rng: &mut Rng, n: usize) -> Vec<Vec<i32>> {
    let mut dominoes = Vec::with_capacity(n);
    for _ in 0..n {
        let a = rng.gen_range_i64(1, 9) as i32;
        let b = rng.gen_range_i64(1, 9) as i32;
        dominoes.push(vec![a, b]);
    }
    dominoes
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1128);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |dominoes: Vec<Vec<i32>>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target {
            return;
        }
        let key = format!("{:?}", dominoes);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::num_equiv_domino_pairs(dominoes.clone());
        writeln!(out, "{}", json!({"input": {"dominoes": dominoes}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<Vec<i32>>> = vec![
        vec![vec![1,2], vec![2,1], vec![3,4], vec![5,6]],
        vec![vec![1,2], vec![1,2], vec![1,1], vec![1,2], vec![2,2]],
    ];
    for ex in examples {
        emit(ex, &mut seen, &mut out, &mut count);
    }

    // Hand-crafted seeds
    let seeds: Vec<Vec<Vec<i32>>> = vec![
        vec![vec![1,1]],                                          // single domino
        vec![vec![1,1], vec![1,1]],                               // single pair match
        vec![vec![1,2], vec![3,4]],                               // no match
        vec![vec![9,9], vec![9,9], vec![9,9]],                    // all same
        vec![vec![1,2], vec![2,1]],                               // reversed pair
        vec![vec![1,1], vec![2,2], vec![3,3], vec![4,4]],         // all different self-pairs
        vec![vec![1,9], vec![9,1], vec![1,9]],                    // boundary values equiv
        vec![vec![5,5], vec![5,5], vec![5,5], vec![5,5], vec![5,5]], // all identical
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8];

    // Apply every mutation to every seed
    for s in &seeds {
        for &mk in &mutation_kinds {
            emit(mutate(s.clone(), mk), &mut seen, &mut out, &mut count);
        }
    }

    // Random dominoes with random mutations across size classes
    while count < target {
        let n = match count % 5 {
            0 => rng.gen_range_usize(1, 5),        // tiny
            1 => rng.gen_range_usize(1, 10),       // small
            2 => rng.gen_range_usize(11, 100),     // medium
            3 => rng.gen_range_usize(101, 1000),   // large
            _ => rng.gen_range_usize(1001, 5000),  // big
        };
        let dominoes = random_dominoes(&mut rng, n);
        let mk = rng.gen_range_usize(0, 8) as u8;
        emit(mutate(dominoes, mk), &mut seen, &mut out, &mut count);
    }
}
