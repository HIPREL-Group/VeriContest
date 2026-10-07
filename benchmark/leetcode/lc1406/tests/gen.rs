use vstd::prelude::*;

verus! {

pub fn generate_test_case(stone_value: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= stone_value.len() <= 50_000,
        forall|i: int| 0 <= i < stone_value.len() ==>
            -1000 <= #[trigger] stone_value[i] <= 1000,
    ensures
        1 <= result.len() <= 50_000,
        forall|i: int| 0 <= i < result.len() ==>
            -1000 <= #[trigger] result[i] <= 1000,
{
    if mutation_kind == 0 {
        // identity
        stone_value
    } else if mutation_kind == 1 {
        // nudge first element up
        let mut sv = stone_value;
        if sv[0] < 1000 {
            sv.set(0, sv[0] + 1);
        }
        sv
    } else if mutation_kind == 2 {
        // nudge first element down
        let mut sv = stone_value;
        if sv[0] > -1000 {
            sv.set(0, sv[0] - 1);
        }
        sv
    } else if mutation_kind == 3 {
        // negate first element
        let mut sv = stone_value;
        sv.set(0, -sv[0]);
        sv
    } else if mutation_kind == 4 {
        // set all elements to 0
        let mut sv = stone_value;
        let mut i: usize = 0;
        while i < sv.len()
            invariant
                0 <= i <= sv.len(),
                sv.len() == stone_value.len(),
                1 <= sv.len() <= 50_000,
                forall|j: int| 0 <= j < i ==> sv[j] == 0i32,
                forall|j: int| i <= j < sv.len() ==>
                    -1000 <= #[trigger] sv[j] <= 1000,
            decreases sv.len() - i,
        {
            sv.set(i, 0);
            i += 1;
        }
        sv
    } else if mutation_kind == 5 && stone_value.len() < 50_000 {
        // grow by one element (push 0)
        let mut sv = stone_value;
        sv.push(0);
        sv
    } else if mutation_kind == 6 && stone_value.len() > 1 {
        // shrink by one element (pop)
        let mut sv = stone_value;
        sv.pop();
        sv
    } else if mutation_kind == 7 {
        // set first element to max boundary (1000)
        let mut sv = stone_value;
        sv.set(0, 1000);
        sv
    } else if mutation_kind == 8 {
        // set first element to min boundary (-1000)
        let mut sv = stone_value;
        sv.set(0, -1000);
        sv
    } else if mutation_kind == 9 {
        // set last element to 0
        let mut sv = stone_value;
        let last = sv.len() - 1;
        sv.set(last, 0);
        sv
    } else if mutation_kind == 10 {
        // negate all elements
        let mut sv = stone_value;
        let mut i: usize = 0;
        while i < sv.len()
            invariant
                0 <= i <= sv.len(),
                sv.len() == stone_value.len(),
                1 <= sv.len() <= 50_000,
                forall|j: int| 0 <= j < i ==>
                    sv[j] == -stone_value[j],
                forall|j: int| 0 <= j < i ==>
                    -1000 <= #[trigger] sv[j] <= 1000,
                forall|j: int| i <= j < sv.len() ==>
                    sv[j] == stone_value[j],
                forall|j: int| i <= j < sv.len() ==>
                    -1000 <= #[trigger] sv[j] <= 1000,
            decreases sv.len() - i,
        {
            sv.set(i, -sv[i]);
            i += 1;
        }
        sv
    } else {
        // fallback: identity
        stone_value
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

fn random_stone_values(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut vals = Vec::with_capacity(len);
    for _ in 0..len {
        vals.push(rng.gen_range_i64(-1000, 1000) as i32);
    }
    vals
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1406);
    let count_target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |sv: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= count_target {
            return;
        }
        let key = format!("{:?}", sv);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::stone_game_iii(sv.clone());
        writeln!(out, "{}", json!({"input": {"stoneValue": sv}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from the problem description
    let examples: Vec<Vec<i32>> = vec![
        vec![1, 2, 3, 7],
        vec![1, 2, 3, -9],
        vec![1, 2, 3, 6],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

    // Apply every mutation to every example
    for ex in &examples {
        for &mk in &mutation_kinds {
            let result = mutate(ex.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Interesting seed arrays
    let special_seeds: Vec<Vec<i32>> = vec![
        vec![0],
        vec![1000],
        vec![-1000],
        vec![0, 0, 0],
        vec![1, -1, 1],
        vec![1000, -1000, 1000],
        vec![1, 1, 1, 1, 1, 1],
        vec![-1, -1, -1],
        vec![999, 999, 999],
        vec![1, 2, 3, 4, 5],
    ];
    for seed_arr in &special_seeds {
        for &mk in &mutation_kinds {
            let result = mutate(seed_arr.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds with diverse size classes and random mutations
    while count < count_target {
        let n: usize = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 5),        // tiny
            1 => rng.gen_range_usize(1, 10),        // small
            2 => rng.gen_range_usize(11, 100),      // medium
            3 => rng.gen_range_usize(101, 1000),    // large
            _ => rng.gen_range_usize(1001, 5000),   // very large (capped for speed)
        };
        let sv = random_stone_values(&mut rng, n);
        let mk = rng.gen_range_usize(0, 10) as u8;
        let result = mutate(sv, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }
}
