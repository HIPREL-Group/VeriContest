use vstd::prelude::*;

verus! {

pub fn generate_test_case(stones: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        2 <= stones.len() <= 100_000,
        forall|i: int| 0 <= i < stones.len() ==> -10_000 <= #[trigger] stones[i] <= 10_000,
    ensures
        2 <= result.len() <= 100_000,
        forall|i: int| 0 <= i < result.len() ==> -10_000 <= #[trigger] result[i] <= 10_000,
{
    if mutation_kind == 0 {
        // identity
        stones
    } else if mutation_kind == 1 {
        // set last element to 10_000 (max boundary)
        let mut s = stones;
        let last = s.len() - 1;
        s.set(last, 10_000);
        s
    } else if mutation_kind == 2 {
        // set last element to -10_000 (min boundary)
        let mut s = stones;
        let last = s.len() - 1;
        s.set(last, -10_000);
        s
    } else if mutation_kind == 3 {
        // set all elements to 0
        let mut s = stones;
        let mut i: usize = 0;
        while i < s.len()
            invariant
                0 <= i <= s.len(),
                s.len() == stones.len(),
                2 <= s.len() <= 100_000,
                forall|j: int| 0 <= j < i ==> s[j] == 0i32,
                forall|j: int| i <= j < s.len() ==> s[j] == stones[j],
            decreases s.len() - i,
        {
            s.set(i, 0);
            i += 1;
        }
        s
    } else if mutation_kind == 4 && stones.len() < 100_000 {
        // grow by one element (push 0)
        let mut s = stones;
        s.push(0);
        s
    } else if mutation_kind == 5 && stones.len() > 2 {
        // shrink by one element (pop)
        let mut s = stones;
        s.pop();
        s
    } else if mutation_kind == 6 {
        // nudge last element up (if < 10_000)
        let mut s = stones;
        let last = s.len() - 1;
        if s[last] < 10_000 {
            s.set(last, s[last] + 1);
        }
        s
    } else if mutation_kind == 7 {
        // nudge last element down (if > -10_000)
        let mut s = stones;
        let last = s.len() - 1;
        if s[last] > -10_000 {
            s.set(last, s[last] - 1);
        }
        s
    } else if mutation_kind == 8 {
        // negate first element
        let mut s = stones;
        if s[0] > -10_000 && s[0] < 10_000 {
            s.set(0, -s[0]);
        }
        s
    } else if mutation_kind == 9 && stones.len() >= 2 {
        // swap first and last elements
        let mut s = stones;
        let last = s.len() - 1;
        let tmp = s[0];
        s.set(0, s[last]);
        s.set(last, tmp);
        s
    } else {
        stones // fallback
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

fn mutate(stones: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(stones, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_stones(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut stones = Vec::with_capacity(len);
    for _ in 0..len {
        stones.push(rng.gen_range_i64(-10_000, 10_000) as i32);
    }
    stones
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1872);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);
    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |stones: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target {
            return;
        }
        let key = format!("{:?}", stones);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::stone_game_viii(stones.clone());
        writeln!(out, "{}", json!({"input": {"stones": stones}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![-1, 2, -3, 4, -5],
        vec![7, -6, 5, 10, 5, -2, -6],
        vec![-10, -12],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    // Apply every mutation to every example
    for ex in &examples {
        for &mk in &mutation_kinds {
            let result = mutate(ex.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Interesting seed arrays
    let seeds: Vec<Vec<i32>> = vec![
        vec![0, 0],
        vec![10_000, -10_000],
        vec![-10_000, 10_000],
        vec![0, 0, 0, 0, 0],
        vec![1, -1, 1, -1],
        vec![10_000, 10_000, 10_000],
        vec![-10_000, -10_000, -10_000],
        vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
    ];

    for seed_arr in &seeds {
        for &mk in &mutation_kinds {
            let result = mutate(seed_arr.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds with diverse size classes and random mutations
    while count < target {
        let n: usize = match count % 5 {
            0 => rng.gen_range_usize(2, 5),        // tiny
            1 => rng.gen_range_usize(2, 10),       // small
            2 => rng.gen_range_usize(11, 100),     // medium
            3 => rng.gen_range_usize(101, 1000),   // large
            _ => rng.gen_range_usize(1001, 10_000), // very large
        };
        let stones = random_stones(&mut rng, n);
        let mk = rng.gen_range_usize(0, 9) as u8;
        let result = mutate(stones, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }
}
