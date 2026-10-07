use vstd::prelude::*;

verus! {

pub fn generate_test_case(stone_value: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= stone_value.len() <= 500,
        forall|i: int| 0 <= i < stone_value.len() ==> 1 <= #[trigger] stone_value[i] <= 1_000_000,
    ensures
        1 <= result.len() <= 500,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 1_000_000,
{
    if mutation_kind == 0 {
        // identity
        stone_value
    } else if mutation_kind == 1 {
        // set last element to 1 (min boundary)
        let mut sv = stone_value;
        let last = sv.len() - 1;
        sv.set(last, 1);
        sv
    } else if mutation_kind == 2 {
        // set last element to 1_000_000 (max boundary)
        let mut sv = stone_value;
        let last = sv.len() - 1;
        sv.set(last, 1_000_000);
        sv
    } else if mutation_kind == 3 {
        // set all elements to same value (equal splits)
        let mut sv = stone_value;
        let val = sv[0];
        let mut i: usize = 0;
        while i < sv.len()
            invariant
                0 <= i <= sv.len(),
                sv.len() == stone_value.len(),
                1 <= sv.len() <= 500,
                1 <= val <= 1_000_000,
                forall|j: int| 0 <= j < i ==> sv[j] == val,
                forall|j: int| i <= j < sv.len() ==> sv[j] == stone_value[j],
            decreases sv.len() - i,
        {
            sv.set(i, val);
            i += 1;
        }
        sv
    } else if mutation_kind == 4 && stone_value.len() < 500 {
        // grow by one element
        let mut sv = stone_value;
        sv.push(1);
        sv
    } else if mutation_kind == 5 && stone_value.len() > 1 {
        // shrink by one element
        let mut sv = stone_value;
        sv.pop();
        sv
    } else if mutation_kind == 6 {
        // nudge last element up (if < 1_000_000)
        let mut sv = stone_value;
        let last = sv.len() - 1;
        if sv[last] < 1_000_000 {
            sv.set(last, sv[last] + 1);
        }
        sv
    } else if mutation_kind == 7 {
        // nudge last element down (if > 1)
        let mut sv = stone_value;
        let last = sv.len() - 1;
        if sv[last] > 1 {
            sv.set(last, sv[last] - 1);
        }
        sv
    } else if mutation_kind == 8 && stone_value.len() >= 2 {
        // swap first and last elements
        let mut sv = stone_value;
        let last = sv.len() - 1;
        let first_val = sv[0];
        let last_val = sv[last];
        sv.set(0, last_val);
        if last > 0 {
            sv.set(last, first_val);
        }
        sv
    } else if mutation_kind == 9 {
        // set first element to 1 (min boundary)
        let mut sv = stone_value;
        sv.set(0, 1);
        sv
    } else {
        stone_value // fallback
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

fn mutate(sv: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(sv, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_stone_value(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut sv = Vec::with_capacity(len);
    for _ in 0..len {
        sv.push(rng.gen_range_i64(1, 1_000_000) as i32);
    }
    sv
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1563);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);
    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut emitted = 0usize;

    let mut emit = |sv: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, emitted: &mut usize| {
        if *emitted >= count {
            return;
        }
        let key = format!("{:?}", sv);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::stone_game_v(sv.clone());
        writeln!(out, "{}", json!({"input": {"stoneValue": sv}, "output": output})).unwrap();
        *emitted += 1;
    };

    // Example inputs from description.md
    emit(vec![6, 2, 3, 4, 5, 5], &mut seen, &mut out, &mut emitted);
    emit(vec![7, 7, 7, 7, 7, 7, 7], &mut seen, &mut out, &mut emitted);
    emit(vec![4], &mut seen, &mut out, &mut emitted);

    // Hand-crafted edge cases
    let edge_cases: Vec<Vec<i32>> = vec![
        vec![1],
        vec![1, 1],
        vec![1, 2],
        vec![1_000_000],
        vec![1_000_000, 1_000_000],
        vec![1, 1_000_000],
        vec![1_000_000, 1],
        vec![1, 2, 3],
        vec![3, 2, 1],
        vec![1, 1, 1, 1, 1],
    ];
    for sv in edge_cases {
        emit(sv, &mut seen, &mut out, &mut emitted);
    }

    // Seed pool with mutations
    let seed_pool: Vec<Vec<i32>> = vec![
        vec![6, 2, 3, 4, 5, 5],
        vec![7, 7, 7, 7, 7, 7, 7],
        vec![1, 2, 3, 4, 5],
        vec![5, 4, 3, 2, 1],
        vec![10, 20, 30],
        vec![1, 1, 1],
        vec![1_000_000, 1_000_000, 1_000_000],
    ];
    for sv in &seed_pool {
        for mk in 0u8..=9 {
            emit(mutate(sv.clone(), mk), &mut seen, &mut out, &mut emitted);
        }
    }

    // Random test cases across size classes
    while emitted < count {
        let n: usize = match emitted % 5 {
            0 => rng.gen_range_usize(1, 3),        // tiny
            1 => rng.gen_range_usize(1, 10),       // small
            2 => rng.gen_range_usize(11, 50),      // medium
            3 => rng.gen_range_usize(51, 200),     // large
            _ => rng.gen_range_usize(201, 500),    // max
        };
        let sv = random_stone_value(&mut rng, n);
        let mk = rng.gen_range_usize(0, 10) as u8;
        emit(mutate(sv, mk), &mut seen, &mut out, &mut emitted);
    }
}
