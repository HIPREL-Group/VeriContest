use vstd::prelude::*;

verus! {

pub fn generate_test_case(cards: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= cards.len() <= 100000,
        forall|i: int| 0 <= i < cards.len() ==> 0 <= #[trigger] cards[i] <= 1000000,
    ensures
        1 <= result.len() <= 100000,
        forall|i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] <= 1000000,
{
    if mutation_kind == 0 {
        // identity
        cards
    } else if mutation_kind == 1 {
        // set first element to 0
        let mut c = cards;
        c.set(0, 0);
        c
    } else if mutation_kind == 2 {
        // set first element to max boundary (1000000)
        let mut c = cards;
        c.set(0, 1000000);
        c
    } else if mutation_kind == 3 && cards.len() >= 2 {
        // duplicate first element into second position (guarantees a matching pair)
        let mut c = cards;
        let v = c[0];
        c.set(1, v);
        c
    } else if mutation_kind == 4 && cards.len() < 100000 {
        // grow by one element (push 0)
        let mut c = cards;
        c.push(0);
        c
    } else if mutation_kind == 5 && cards.len() > 1 {
        // shrink by one element (pop)
        let mut c = cards;
        c.pop();
        c
    } else if mutation_kind == 6 {
        // set all elements to the same value (all matching)
        let mut c = cards;
        let mut i: usize = 0;
        while i < c.len()
            invariant
                0 <= i <= c.len(),
                c.len() == cards.len(),
                1 <= c.len() <= 100000,
                forall|j: int| 0 <= j < i ==> c[j] == 0,
                forall|j: int| i <= j < c.len() ==> c[j] == cards[j],
            decreases c.len() - i,
        {
            c.set(i, 0);
            i += 1;
        }
        c
    } else if mutation_kind == 7 && cards.len() >= 2 {
        // swap first and last elements
        let mut c = cards;
        let first = c[0];
        let last_idx = c.len() - 1;
        let last = c[last_idx];
        c.set(0, last);
        c.set(last_idx, first);
        c
    } else if mutation_kind == 8 {
        // nudge first element up: if < 1000000, increment by 1
        let mut c = cards;
        if c[0] < 1000000 {
            c.set(0, c[0] + 1);
        }
        c
    } else if mutation_kind == 9 {
        // nudge first element down: if > 0, decrement by 1
        let mut c = cards;
        if c[0] > 0 {
            c.set(0, c[0] - 1);
        }
        c
    } else if mutation_kind == 10 && cards.len() >= 2 {
        // duplicate last element into second-to-last (matching pair at end)
        let mut c = cards;
        let last_idx = c.len() - 1;
        let v = c[last_idx];
        c.set(last_idx - 1, v);
        c
    } else {
        cards  // fallback
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

fn mutate(cards: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(cards, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_cards(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut cards = Vec::with_capacity(len);
    for _ in 0..len {
        cards.push(rng.gen_range_i64(0, 1000000) as i32);
    }
    cards
}

fn random_cards_with_match(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut cards = random_cards(rng, len);
    if len >= 2 {
        let pos1 = rng.gen_range_usize(0, len - 1);
        let mut pos2 = rng.gen_range_usize(0, len - 1);
        while pos2 == pos1 {
            pos2 = rng.gen_range_usize(0, len - 1);
        }
        cards[pos2] = cards[pos1];
    }
    cards
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2260);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |cards: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count {
            return;
        }
        let key = format!("{:?}", cards);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::minimum_card_pickup(cards.clone());
        writeln!(out, "{}", json!({"input": {"cards": cards}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let example_seeds: Vec<Vec<i32>> = vec![
        vec![3, 4, 2, 3, 4, 7],
        vec![1, 0, 5, 3],
    ];

    let mutation_kinds: Vec<u8> = (0..=10).collect();

    // Apply every mutation to every example seed
    for seed_cards in &example_seeds {
        for &mk in &mutation_kinds {
            let result = mutate(seed_cards.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Boundary seeds
    let boundary_seeds: Vec<Vec<i32>> = vec![
        vec![0],                                   // single element, min value
        vec![1000000],                             // single element, max value
        vec![0, 0],                                // two identical elements
        vec![0, 1],                                // two different elements
        vec![1000000, 1000000],                    // two identical max elements
        vec![5, 5, 5, 5, 5],                       // all same
        vec![1, 2, 3, 4, 5, 1],                    // match at ends
        vec![1, 2, 1, 3, 2, 3],                    // multiple matches
    ];

    for seed_cards in &boundary_seeds {
        for &mk in &mutation_kinds {
            let result = mutate(seed_cards.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds across size classes with random mutations
    for i in 0..80 {
        let n: usize = match i % 5 {
            0 => rng.gen_range_usize(1, 5),        // tiny
            1 => rng.gen_range_usize(1, 10),       // small
            2 => rng.gen_range_usize(11, 100),     // medium
            3 => rng.gen_range_usize(101, 1000),   // large
            _ => rng.gen_range_usize(1001, 10000), // very large
        };
        // Alternate between random cards and cards with guaranteed match
        let seed_cards = if i % 2 == 0 {
            random_cards(&mut rng, n)
        } else {
            random_cards_with_match(&mut rng, n)
        };
        let mk = rng.gen_range_usize(0, 10) as u8;
        let result = mutate(seed_cards, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }

    // Fill remaining with identity mutation on random inputs
    while count < target_count {
        let n = rng.gen_range_usize(1, 1000);
        let seed_cards = if count % 3 == 0 {
            random_cards_with_match(&mut rng, n)
        } else {
            random_cards(&mut rng, n)
        };
        emit(mutate(seed_cards, 0), &mut seen, &mut out, &mut count);
    }
}
