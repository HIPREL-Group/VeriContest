use vstd::prelude::*;

verus! {

pub fn generate_test_case(stones: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= stones.len() <= 30,
        forall|i: int| 0 <= i < stones.len() ==> 1 <= #[trigger] stones[i] <= 100,
    ensures
        1 <= result.len() <= 30,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 100,
{
    if mutation_kind == 0 {
        // identity
        stones
    } else if mutation_kind == 1 {
        // set last element to 1 (min boundary)
        let mut s = stones;
        let last = s.len() - 1;
        s.set(last, 1);
        s
    } else if mutation_kind == 2 {
        // set last element to 100 (max boundary)
        let mut s = stones;
        let last = s.len() - 1;
        s.set(last, 100);
        s
    } else if mutation_kind == 3 && stones.len() < 30 {
        // grow: append element with value 50
        let mut s = stones;
        s.push(50);
        s
    } else if mutation_kind == 4 && stones.len() > 1 {
        // shrink: remove last element
        let mut s = stones;
        s.pop();
        s
    } else if mutation_kind == 5 {
        // set all elements to 1
        let mut s = stones;
        let mut i: usize = 0;
        while i < s.len()
            invariant
                0 <= i <= s.len(),
                s.len() == stones.len(),
                1 <= s.len() <= 30,
                forall|j: int| 0 <= j < i ==> s[j] == 1i32,
                forall|j: int| i <= j < s.len() ==> s[j] == stones[j],
            decreases s.len() - i,
        {
            s.set(i, 1);
            i += 1;
        }
        s
    } else if mutation_kind == 6 {
        // set all elements to 100
        let mut s = stones;
        let mut i: usize = 0;
        while i < s.len()
            invariant
                0 <= i <= s.len(),
                s.len() == stones.len(),
                1 <= s.len() <= 30,
                forall|j: int| 0 <= j < i ==> s[j] == 100i32,
                forall|j: int| i <= j < s.len() ==> s[j] == stones[j],
            decreases s.len() - i,
        {
            s.set(i, 100);
            i += 1;
        }
        s
    } else if mutation_kind == 7 {
        // nudge last element up (if < 100)
        let mut s = stones;
        let last = s.len() - 1;
        if s[last] < 100 {
            s.set(last, s[last] + 1);
        }
        s
    } else if mutation_kind == 8 {
        // nudge last element down (if > 1)
        let mut s = stones;
        let last = s.len() - 1;
        if s[last] > 1 {
            s.set(last, s[last] - 1);
        }
        s
    } else if mutation_kind == 9 && stones.len() >= 2 {
        // swap first and last elements
        let mut s = stones;
        let last = s.len() - 1;
        let first_val = s[0];
        let last_val = s[last];
        s.set(0, last_val);
        if last > 0 {
            s.set(last, first_val);
        }
        s
    } else {
        // fallback: identity
        stones
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

fn mutate(stones: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(stones, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_stones(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut stones = Vec::with_capacity(len);
    for _ in 0..len {
        stones.push(rng.gen_range_i64(1, 100) as i32);
    }
    stones
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |stones: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count {
            return;
        }
        let key = format!("{:?}", stones);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::last_stone_weight_ii(stones.clone());
        writeln!(out, "{}", json!({"input": {"stones": stones}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![2, 7, 4, 1, 8, 1],
        vec![31, 26, 33, 21, 40],
    ];

    // Seed pool: boundary and interesting cases
    let seeds: Vec<Vec<i32>> = vec![
        vec![1],
        vec![100],
        vec![1, 1],
        vec![1, 100],
        vec![100, 100],
        vec![50, 50, 50],
        vec![1, 2, 3, 4, 5],
        vec![100, 99, 98, 97, 96],
        vec![1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
        vec![100, 100, 100, 100, 100, 100, 100, 100, 100, 100],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    // Emit examples with identity mutation
    for ex in &examples {
        emit(ex.clone(), &mut seen, &mut out, &mut count);
    }

    // Apply every mutation to every seed
    for s in &seeds {
        for &mk in &mutation_kinds {
            let result = mutate(s.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds with varied sizes and random mutations
    for i in 0..80 {
        let len = match i % 5 {
            0 => rng.gen_range_usize(1, 3),    // tiny
            1 => rng.gen_range_usize(1, 5),    // small
            2 => rng.gen_range_usize(5, 10),   // medium
            3 => rng.gen_range_usize(10, 20),  // large
            _ => rng.gen_range_usize(20, 30),  // max
        };
        let s = random_stones(&mut rng, len);
        let mk = rng.gen_range_usize(0, 9) as u8;
        let result = mutate(s, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }

    // Fill remaining with random identity
    while count < target_count {
        let len = rng.gen_range_usize(1, 30);
        let s = random_stones(&mut rng, len);
        emit(mutate(s, 0), &mut seen, &mut out, &mut count);
    }
}
